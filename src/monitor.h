#ifndef __MONITOR_H__
#define __MONITOR_H__

#include "DFA.h"
#include "formula.h"
#include "util.h"

#include <algorithm>
#include <exception>
#include <optional>
#include <stdexcept>
#include <vector>


#define memL(t1, t2, f, t) ((f) <= (t2) - (t1))
#define memR(t1, t2, f, t) ((t2) - (t1) <= (t))
#define mem(t1, t2, f, t) (memL(t1, t2, f, t) && memR(t1, t2, f, t))

class Monitor {
public:
    bool eof = false;

    virtual ~Monitor() {}
    virtual Monitor *clone() = 0;
    BooleanVerdict step() {
        if (eof) {
            throw EOL();
        } else {
            try {
                return step_impl();
            } catch (const EOL &e) {
                eof = true;
                throw EOL();
            }
        }
    }
    virtual BooleanVerdict step_impl() = 0;
};

class EvalMonitor : public Monitor {
    Formula *fmla;
    InputReader *input_reader;
    Event *handle;

public:
    EvalMonitor(Formula *fmla, InputReader *input_reader, Event *handle) : fmla(fmla), input_reader(input_reader), handle(handle) {}
    Monitor *clone() override {
        return new EvalMonitor(fmla, input_reader, handle->clone());
    }
    BooleanVerdict step_impl() override {
        bool b = fmla->eval(handle);
        return BooleanVerdict(handle->ts, b ? TRUE : FALSE);
    }
};

class LastReader {
    std::vector<Formula *> fmla;
    InputReader *input_reader;
    Event *handle;
    std::vector<Monitor *> sub_mon;

public:
    int eof;
    std::vector<vector<int> > sub_es;

    size_t buf_len, buf_len_mask;
    size_t buf_beg, buf_end;

    LastReader(const vector<Formula *> &fmla, InputReader *input_reader, Event *handle, const std::vector<Monitor *> &sub_mon, size_t buf_len) : fmla(fmla), input_reader(input_reader), handle(handle), sub_mon(sub_mon), eof(0), buf_len(buf_len), buf_len_mask((1 << buf_len) - 1) {
        sub_es.resize(1 << buf_len);
        for (size_t i = 0; i < sub_es.size(); i++) sub_es[i].resize(fmla.size());
        buf_beg = buf_end = 0;
    }
    LastReader(LastReader *l_reader) : fmla(l_reader->fmla), input_reader(l_reader->input_reader), handle(l_reader->handle->clone()), eof(l_reader->eof), buf_len(l_reader->buf_len), buf_len_mask(l_reader->buf_len_mask), buf_beg(l_reader->buf_beg), buf_end(l_reader->buf_end) {
        for (size_t i = 0; i < fmla.size(); i++) {
            if (fmla[i]->is_temporal) {
                sub_mon.push_back(l_reader->sub_mon[i]->clone());
            } else {
                sub_mon.push_back(new EvalMonitor(fmla[i], input_reader, handle));
            }
        }
        sub_es.resize(1 << buf_len);
        for (size_t i = 0; i < sub_es.size(); i++) sub_es[i] = l_reader->sub_es[i];
    }
    ~LastReader() {
        for (size_t i = 0; i < sub_mon.size(); i++) delete sub_mon[i];
    }

    void run() {
        if (eof) return;
        input_reader->read_handle(handle);
        size_t buf_end_mod = buf_end & buf_len_mask;
        try {
          for (size_t i = 0; i < fmla.size(); i++) {
              BooleanVerdict v = sub_mon[i]->step();
              sub_es[buf_end_mod][i] = (v.b == TRUE);
          }
          buf_end++;
        } catch (const EOL &e) {
          eof = 1;
        }
    }
};

class MH_FW {
protected:
    DFA *dfa;
    InputReader *input_reader;
    Event *b_head, *f_head;
    LastReader *b_reader, *f_reader;

    // auxiliary storage
    // invariant: seen[i] == -1 for all i
    std::vector<int> seen;

    // used by run_back()
    struct CurEntry {
        DState *q;                                          // current state in the run from dfa->init
        std::optional<std::pair<timestamp, int> > last_sat; // last satisfaction in the run from dfa->init
    } cur;

    struct QMapEntry {
        DState *q;                                                // used by run_back()
        std::optional<std::pair<timestamp, int> > last_sat = {};  // last satisfaction before end time-point
        DState *end_q;                                            // state at end time-point

        QMapEntry() {}
        QMapEntry(const std::optional<std::pair<timestamp, int> > &last_sat, DState *end_q) : last_sat(last_sat), end_q(end_q) {}
    };

    // q_map
    std::vector<std::pair<DState *, QMapEntry> > q_map;
    size_t q_map_init;

    int back_tp, front_tp;

    void rescale_seen() {
        seen.resize(dfa->get_cnt(), -1);
    }
    vector<int> back_es() {
        CHECK(b_reader->buf_beg != b_reader->buf_end || b_reader->eof);
        if (b_reader->buf_beg == b_reader->buf_end) throw EOL();
        return b_reader->sub_es[b_reader->buf_beg & b_reader->buf_len_mask];
    }
    vector<int> front_es() {
        if (f_reader == NULL) {
          if (b_reader->eof) throw EOL();
          return b_reader->sub_es[(b_reader->buf_end - 1) & b_reader->buf_len_mask];
        } else {
          if (f_reader->eof) throw EOL();
          return f_reader->sub_es[(f_reader->buf_end - 1) & f_reader->buf_len_mask];
        }
    }
    void run_ms_front() {
        if (b_reader->buf_end - b_reader->buf_beg < (1 << b_reader->buf_len)) {
            CHECK(b_reader->buf_end - 1 == front_tp);
            b_reader->run();
        } else if (f_reader == NULL) {
            CHECK(b_reader->buf_end - 1 == front_tp);
            f_reader = new LastReader(b_reader);
        }
        if (f_reader != NULL) {
            f_reader->run();
        }
    }
    void run_ms_back() {
        b_reader->buf_beg++;
        if (b_reader->buf_end - 1 < front_tp) {
            b_reader->run();
        }
    }

    MH_FW(MH_FW *s) : dfa(s->dfa), input_reader(s->input_reader), b_head(s->b_head->clone()), f_head(s->f_head->clone()), b_reader(new LastReader(s->b_reader)), seen(s->seen), q_map(s->q_map), q_map_init(s->q_map_init) {
        if (s->f_reader != NULL) f_reader = new LastReader(s->f_reader);
        else f_reader = NULL;

        back_tp = s->back_tp;
        front_tp = s->front_tp;
    }

public:
    MH_FW(DFA *dfa, InputReader *input_reader, LastReader *l_reader) : dfa(dfa), input_reader(input_reader), b_reader(l_reader) {
        b_head = input_reader->open_handle();
        input_reader->read_handle(b_head);
        f_head = input_reader->open_handle();
        input_reader->read_handle(f_head);

        b_reader->run();
        f_reader = NULL;

        q_map.push_back(std::make_pair(dfa->empty, QMapEntry(std::nullopt, dfa->empty)));
        q_map.push_back(std::make_pair(dfa->init, QMapEntry(std::nullopt, dfa->init)));
        q_map_init = 1;
        back_tp = front_tp = 0;
        CHECK(q_map[q_map_init].first == dfa->init);
    }
    ~MH_FW() {
        delete b_reader;
        if (f_reader) delete f_reader;
    }
    virtual MH_FW *clone() {
        return new MH_FW(this);
    }
    BooleanVerdict check_fw(timestamp from, timestamp to) {
        if (b_head->eof) throw EOL();
        timestamp t = b_head->ts;
        while (!f_head->eof && memR(t, f_head->ts, from, to)) {
            run_front();
        }
        if (f_head->eof) throw EOL();
        QMapEntry *e = &q_map[q_map_init].second;
        Boolean b = FALSE;
        if (e->last_sat && memL(t, e->last_sat->first, from, to)) b = TRUE;
        run_back();
        return BooleanVerdict(t, b);
    }
    virtual void run_front() {
        if (f_head->eof) throw EOL();
        timestamp tj = f_head->ts;
        input_reader->read_handle(f_head);
        vector<int> bj = front_es();
        run_ms_front();

        for (size_t i = 0; i < q_map.size(); i++) {
            QMapEntry *e = &q_map[i].second;
            e->end_q = dfa->run(e->end_q, bj);
            if (e->end_q->accept) e->last_sat = std::make_pair(tj, front_tp);
        }
        front_tp++;
    }
    virtual void run_back() {
        CHECK(!b_head->eof);
        timestamp ti = b_head->ts;
        input_reader->read_handle(b_head);

        const vector<int> bi = back_es();
        run_ms_back();

        for (size_t i = 0; i < q_map.size(); i++) {
            q_map[i].first = dfa->run(q_map[i].first, bi);
            q_map[i].second.q = q_map[i].first; // initialize a fresh run
            if (q_map[i].second.last_sat && q_map[i].second.last_sat->second == back_tp) {
                q_map[i].second.last_sat = {};
            }
        }

        // remove duplicates in q_map
        size_t idx = 0;
        rescale_seen();
        for (size_t i = 0; i < q_map.size(); i++) {
            DState *st = q_map[i].first;
            if (seen[st->idx] == -1) {
                seen[st->idx] = 1;
                q_map[idx++] = q_map[i];
            }
        }
        // reset seen to an empty map and look for dfa->init
        int init_found = 0;
        for (size_t i = 0; i < idx; i++) {
            DState *st = q_map[i].first;
            if (st == dfa->init) {
                q_map_init = i;
                init_found = 1;
            }
            seen[st->idx] = -1;
        }
        q_map.resize(idx);

        back_tp++;

        if (init_found) return;

        // current state is not in q_map
        cur.q = dfa->init;
        cur.last_sat = {};
        size_t cur_tp = back_tp;
        Event *c_head = b_head->clone();
        LastReader *c_reader = NULL;

        // run current state until end time-point or collapse
        while (cur_tp < front_tp) {
            int found = 0;
            for (size_t i = 0; !found && i < q_map.size(); i++) {
                QMapEntry *e = &q_map[i].second;
                if (e->q == cur.q) {
                    cur.q = e->end_q;
                    if (e->last_sat && e->last_sat->second >= cur_tp) cur.last_sat = e->last_sat;
                    found = 1;
                }
            }
            if (found) break;

            CHECK(!c_head->eof);
            timestamp tcur = c_head->ts;
            input_reader->read_handle(c_head);
            vector<int> b_cur;
            if (cur_tp < b_reader->buf_end - 1) {
                b_cur = b_reader->sub_es[cur_tp & b_reader->buf_len_mask];
            } else {
                if (c_reader == NULL) {
                    CHECK(cur_tp == b_reader->buf_end - 1);
                    c_reader = new LastReader(b_reader);
                }
                b_cur = c_reader->sub_es[cur_tp & c_reader->buf_len_mask];
            }
            if (c_reader != NULL) {
              c_reader->run();
            }

            cur.q = dfa->run(cur.q, b_cur);
            if (cur.q->accept) cur.last_sat = std::make_pair(tcur, cur_tp);

            for (size_t i = 0; i < q_map.size(); i++) {
                q_map[i].second.q = dfa->run(q_map[i].second.q, b_cur);
            }

            cur_tp++;
        }
        delete c_head;
        if (c_reader != NULL) delete c_reader;

        q_map_init = q_map.size();
        q_map.push_back(std::make_pair(dfa->init, QMapEntry(cur.last_sat, cur.q)));
    }
};

class MH_BW : public MH_FW {
    // latest matching suffix (for BwMonitor)
    std::vector<std::pair<DState *, std::pair<timestamp, int> > > e_map;

    void e_map_add(DState *s, std::pair<timestamp, int> tsp) {
        for (size_t i = 0; i < e_map.size(); i++) {
            if (e_map[i].first == s) {
                e_map[i].second = tsp;
                return;
            }
        }
        e_map.push_back(std::make_pair(s, tsp));
    }

    MH_BW(MH_BW *s) : MH_FW(s), e_map(s->e_map) {}

public:
    MH_BW(DFA *dfa, InputReader *input_reader, LastReader *l_reader) : MH_FW(dfa, input_reader, l_reader) {}
    virtual MH_BW *clone() override {
        return new MH_BW(this);
    }
    BooleanVerdict check_bw(timestamp from, timestamp to) {
        if (f_head->eof) throw EOL();
        timestamp t = f_head->ts;

        run_front();

        while (back_tp < front_tp && memL(b_head->ts, t, from, to)) {
            run_back();
        }
        Boolean b = FALSE;
        for (size_t i = 0; b == FALSE && i < e_map.size(); i++) {
            if (e_map[i].first->accept && memR(e_map[i].second.first, t, from, to)) b = TRUE;
        }
        return BooleanVerdict(t, b);
    }
    virtual void run_front() override {
        CHECK(!q_map.empty());

        if (f_head->eof) throw EOL();
        vector<int> bj = front_es();

        size_t idx = 0;
        for (size_t i = 0; i < e_map.size(); i++) {
            e_map[i].first = dfa->run(e_map[i].first, bj);
        }
        rescale_seen();
        for (size_t i = 0; i < e_map.size(); i++) {
            DState *st = e_map[i].first;
            if (seen[st->idx] == -1) {
                seen[st->idx] = idx;
                e_map[idx++] = e_map[i];
            } else if (e_map[i].second.second > e_map[seen[st->idx]].second.second) {
                e_map[seen[st->idx]].second = e_map[i].second;
            }
        }
        for (size_t i = 0; i < idx; i++) {
            DState *st = e_map[i].first;
            seen[st->idx] = -1;
        }
        e_map.resize(idx);

        MH_FW::run_front();
    }
    virtual void run_back() override {
        CHECK(!q_map.empty());
        CHECK(!b_head->eof);

        e_map_add(q_map[q_map_init].second.end_q, std::pair(b_head->ts, back_tp));

        MH_FW::run_back();
    }
};

class BwMonitor : public Monitor {
    timestamp from, to;
    DFA *dfa;
    int dfa_owner;

    MH_BW *s;

public:
    BwMonitor(timestamp from, timestamp to, DFA *dfa, MH_BW *s, int dfa_owner = 1) : from(from), to(to), dfa(dfa), dfa_owner(dfa_owner), s(s) {}
    ~BwMonitor() {
        if (dfa_owner) delete dfa;
        delete s;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

class FwMonitor : public Monitor {
    timestamp from, to;
    DFA *dfa;
    int dfa_owner;

    MH_FW *s;

public:
    FwMonitor(timestamp from, timestamp to, DFA *dfa, MH_FW *s, int dfa_owner = 1) : from(from), to(to), dfa(dfa), dfa_owner(dfa_owner), s(s) {}
    ~FwMonitor() {
        if (dfa_owner) delete dfa;
        delete s;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

class NonTempMonitor : public Monitor {
    Formula *fmla;
    int fmla_owner;
    InputReader *input_reader;
    Event *handle;

public:
    NonTempMonitor(Formula *fmla, InputReader *input_reader, Event *handle, int fmla_owner = 0) : fmla(fmla), input_reader(input_reader), handle(handle), fmla_owner(fmla_owner) {}
    ~NonTempMonitor() {
        if (fmla_owner) delete fmla;
        delete handle;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

class NegMonitor : public Monitor {
    Monitor *subf;

public:
    NegMonitor(Monitor *subf) : subf(subf) {}
    ~NegMonitor() {
        delete subf;
    }
    Monitor *clone() override {
        return new NegMonitor(subf->clone());
    }
    BooleanVerdict step_impl() override {
        return !subf->step();
    }
};

class AndMonitor : public Monitor {
    Monitor *subf, *subg;

public:
    AndMonitor(Monitor *subf, Monitor *subg) : subf(subf), subg(subg) {}
    ~AndMonitor() {
        delete subf;
        delete subg;
    }
    Monitor *clone() override {
        return new AndMonitor(subf->clone(), subg->clone());
    }
    BooleanVerdict step_impl() override {
        return subf->step() && subg->step();
    }
};

class OrMonitor : public Monitor {
    Monitor *subf, *subg;

public:
    OrMonitor(Monitor *subf, Monitor *subg) : subf(subf), subg(subg) {}
    ~OrMonitor() {
        delete subf;
        delete subg;
    }
    Monitor *clone() override {
        return new OrMonitor(subf->clone(), subg->clone());
    }
    BooleanVerdict step_impl() override {
        return subf->step() || subg->step();
    }
};

class PrevMonitor : public Monitor {
    timestamp from, to;
    Monitor *subf;
    InputReader *input_reader;
    Event *handle;
    std::optional<BooleanVerdict> v;

public:
    PrevMonitor(InputReader *input_reader, Event *handle, Monitor *subf, timestamp from, timestamp to) : from(from), to(to), subf(subf), input_reader(input_reader), handle(handle) {}
    ~PrevMonitor() {
        delete subf;
        delete handle;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

class NextMonitor : public Monitor {
    timestamp from, to;
    Monitor *subf;
    InputReader *input_reader;
    Event *handle;
    std::optional<timestamp> t;

public:
    NextMonitor(InputReader *input_reader, Event *handle, Monitor *subf, timestamp from, timestamp to) : from(from), to(to), subf(subf), input_reader(input_reader), handle(handle) {}
    ~NextMonitor() {
        delete subf;
        delete handle;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

class SinceMonitor : public Monitor {
    timestamp from, to;
    Monitor *subf, *subg;
    InputReader *input_reader;
    Event *handle;
    int cphi, cpsi;
    std::optional<int> ocpsi;
    std::optional<timestamp> otpsi;

public:
    SinceMonitor(InputReader *input_reader, Event *handle, Monitor *subf, Monitor *subg, timestamp from, timestamp to) : from(from), to(to), subf(subf), subg(subg), input_reader(input_reader), handle(handle), cphi(0), cpsi(0) {
        ocpsi = {};
        otpsi = {};
        input_reader->read_handle(handle);
    }
    ~SinceMonitor() {
        delete subf;
        delete subg;
        delete handle;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

class UntilMonitor : public Monitor {
    timestamp from, to;
    Monitor *subf, *subg;
    InputReader *input_reader;
    Event *front, *back;
    int c;
    std::optional<std::pair<timestamp, std::pair<Boolean, Boolean> > > z;

    bool loopCondUntil() const {
        if (c != 0) {
            if (z) {
                if ((z->second.second && memL(back->ts, z->first, from, to)) || !z->second.first) return false;
            }
        }
        if (front->eof) return false;
        else return memR(back->ts, front->ts, from, to);
    }

public:
    UntilMonitor(InputReader *input_reader, Event *front, Event *back, Monitor *subf, Monitor *subg, timestamp from, timestamp to) : from(from), to(to), subf(subf), subg(subg), input_reader(input_reader), front(front), back(back), c(0) {
        input_reader->read_handle(front);
        z = {};
    }
    ~UntilMonitor() {
        delete subf;
        delete subg;
        delete front;
        delete back;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

#endif /* __MONITOR_H__ */
