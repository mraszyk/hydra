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

struct Formula;

class Monitor {
public:
    bool eof = false;

    virtual ~Monitor() {}
    virtual Monitor *clone() = 0;
    BooleanVerdict step() {
        if (eof) {
            throw EOL();
        } else {
            return step_impl();
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
    InputReader *input_reader;

    std::vector<Formula *> fmla;
    Event *ap_handle;
    std::vector<Monitor *> sub_mon;

public:
    int unresolved;

    std::vector<Event *> sub_es;

    size_t buf_len, buf_len_mask;
    size_t buf_beg, buf_end;

    LastReader(InputReader *input_reader, const vector<Formula *> &fmla, Event *ap_handle, const std::vector<Monitor *> &sub_mon, size_t buf_len) : input_reader(input_reader), fmla(fmla), ap_handle(ap_handle), sub_mon(sub_mon), unresolved(0), buf_len(buf_len), buf_len_mask((1 << buf_len) - 1) {
        sub_es.resize(1 << buf_len);
        for (size_t i = 0; i < (1 << buf_len); i++) sub_es[i] = new Event(fmla.size());
        buf_beg = buf_end = 0;
    }
    LastReader(LastReader *l_reader) : input_reader(l_reader->input_reader), fmla(l_reader->fmla), unresolved(l_reader->unresolved), buf_len(l_reader->buf_len), buf_len_mask(l_reader->buf_len_mask), buf_beg(l_reader->buf_beg), buf_end(l_reader->buf_end) {
        ap_handle = l_reader->ap_handle->clone();
        for (size_t i = 0; i < fmla.size(); i++) {
            if (fmla[i]->is_temporal) {
                sub_mon.push_back(l_reader->sub_mon[i]->clone());
            } else {
                sub_mon.push_back(new EvalMonitor(fmla[i], input_reader, ap_handle));
            }
        }
        sub_es.resize(1 << buf_len);
        for (size_t i = 0; i < (1 << buf_len); i++) sub_es[i] = new Event(l_reader->sub_es[i]);
    }
    ~LastReader() {
        delete ap_handle;
        for (size_t i = 0; i < sub_mon.size(); i++) delete sub_mon[i];
        for (size_t i = 0; i < sub_es.size(); i++) delete sub_es[i];
    }

    void run() {
        if (ap_handle->eof) return;
        size_t buf_end_mod = buf_end & buf_len_mask;
        try {
            input_reader->read_handle(ap_handle);
            for (size_t i = 0; i < fmla.size(); i++) {
                BooleanVerdict v = sub_mon[i]->step();
                if (v.b == UNRESOLVED) unresolved = 1;
                else sub_es[buf_end_mod]->ap_lookup[i] = (v.b == TRUE);
            }
        } catch(const EOL &e) {}
        sub_es[buf_end_mod]->ts = ap_handle->ts;
        sub_es[buf_end_mod]->tp = ap_handle->tp;
        sub_es[buf_end_mod]->eof = ap_handle->eof;
        buf_end++;
    }
};

class MH_FW {
protected:
    DFA *dfa;
    LastReader *b_reader, *f_reader;
    int unresolved;

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
        std::optional<std::pair<timestamp, int> > last_sat = {}; // last satisfaction before end time-point
        DState *end_q;                                            // state at end time-point

        QMapEntry() {}
        QMapEntry(const std::optional<std::pair<timestamp, int> > &last_sat, DState *end_q) : last_sat(last_sat), end_q(end_q) {}
    };

    // q_map
    std::vector<std::pair<DState *, QMapEntry> > q_map;
    size_t q_map_init;

    timestamp back_ts, front_ts;
    int back_tp, front_tp;

    DState *e_closure(DState *q, const Event *e) {
        return dfa->run(q, e);
    }
    bool acc(DState *q, const Event *e) {
        return e_closure(q, e)->accept;
    }
    DState *step(DState *q, const Event *e) {
        return dfa->step(e_closure(q, e));
    }
    std::pair<DState *, bool> step_acc(DState *q, const Event *e) {
        DState *e_closure_state = e_closure(q, e);
        return std::make_pair(dfa->step(e_closure_state), e_closure_state->accept);
    }
    void rescale_seen() {
        seen.resize(dfa->get_cnt(), -1);
    }
    const Event *back_es() {
        return b_reader->sub_es[b_reader->buf_beg & b_reader->buf_len_mask];
    }
    const Event *front_es() {
        if (b_reader->sub_es[(b_reader->buf_end - 1) & b_reader->buf_len_mask]->tp == front_tp) return b_reader->sub_es[(b_reader->buf_end - 1) & b_reader->buf_len_mask];
        else return f_reader->sub_es[(f_reader->buf_end - 1) & f_reader->buf_len_mask];
    }

    MH_FW(MH_FW *s) : dfa(s->dfa), b_reader(new LastReader(s->b_reader)), unresolved(s->unresolved), seen(s->seen), q_map(s->q_map), q_map_init(s->q_map_init) {
        if (s->f_reader != NULL) f_reader = new LastReader(s->f_reader);
        else f_reader = NULL;

        back_ts = s->back_ts;
        front_ts = s->front_ts;
        back_tp = s->back_tp;
        front_tp = s->front_tp;
    }

public:
    MH_FW(DFA *dfa, LastReader *l_reader) : dfa(dfa), b_reader(l_reader) {
        b_reader->run();
        CHECK(b_reader->buf_beg == 0);
        back_ts = b_reader->sub_es[0]->ts;
        front_ts = b_reader->sub_es[0]->ts;
        f_reader = NULL;
        unresolved = b_reader->unresolved;

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
    Boolean check_init_ts(timestamp from) {
        QMapEntry *e = &q_map[q_map_init].second;
        if (e->last_sat && e->last_sat->first - back_ts >= from) return TRUE;
        else return UNRESOLVED;
    }
    Boolean check_init_tp() {
        QMapEntry *e = &q_map[q_map_init].second;
        if (e->last_sat && e->last_sat->second == front_tp) return TRUE;
        else return FALSE;
    }
    BooleanVerdict check_fw(timestamp from, timestamp to) {
        assert(!back_eof());
        timestamp t = back_ts;
        Boolean b = check_init_ts(from);
        while (!front_eof() && front_ts - back_ts <= to) {
            if (b_reader->unresolved || (f_reader && f_reader->unresolved)) unresolved = 1;
            run_front();
            b = check_init_ts(from);
        }
        if (front_eof()) unresolved = 1;
        else if (b == UNRESOLVED) b = FALSE;
        run_back();
        if (unresolved) b = UNRESOLVED;
        return BooleanVerdict(t, b);
    }
    BooleanVerdict check_fw_shift(timestamp delta) {
        assert(!back_eof());
        timestamp t = back_ts;
        Boolean b = UNRESOLVED;
        while (!front_eof() && front_ts - back_ts <= delta) {
            if (b_reader->unresolved || (f_reader && f_reader->unresolved)) unresolved = 1;
            b = check_init_tp();
            run_front();
        }
        if (front_eof()) unresolved = 1;
        run_back();
        if (unresolved) b = UNRESOLVED;
        return BooleanVerdict(t, b);
    }
    int front_eof() {
        if (b_reader->sub_es[(b_reader->buf_end - 1) & b_reader->buf_len_mask]->tp == front_tp) return b_reader->sub_es[(b_reader->buf_end - 1) & b_reader->buf_len_mask]->eof;
        else return f_reader->sub_es[(f_reader->buf_end - 1) & f_reader->buf_len_mask]->eof;
    }
    int back_eof() {
        return b_reader->sub_es[b_reader->buf_beg & b_reader->buf_len_mask]->eof;
    }
    virtual void run_front() {
        CHECK(!q_map.empty());
        CHECK(!front_eof());

        const Event *cur_front_es = front_es();
        timestamp cur_front_ts = front_ts;
        size_t cur_front_tp = front_tp;

        for (size_t i = 0; i < q_map.size(); i++) {
            QMapEntry *e = &q_map[i].second;
            std::pair<DState *, bool> q_new_pair = step_acc(e->end_q, cur_front_es);
            e->end_q = q_new_pair.first;
            if (q_new_pair.second) e->last_sat = std::make_pair(cur_front_ts, cur_front_tp);
        }

        if (b_reader->buf_end - b_reader->buf_beg < (1 << b_reader->buf_len)) {
            CHECK(b_reader->buf_end - 1 == front_tp);
            b_reader->run();
            if (f_reader == NULL) {
                front_tp = b_reader->sub_es[(b_reader->buf_end - 1) & b_reader->buf_len_mask]->tp;
                front_ts = b_reader->sub_es[(b_reader->buf_end - 1) & b_reader->buf_len_mask]->ts;
            }
        } else if (f_reader == NULL) {
            CHECK(b_reader->buf_end - 1 == front_tp);
            f_reader = new LastReader(b_reader);
        }
        if (f_reader != NULL) {
            f_reader->run();
            front_tp = f_reader->sub_es[(f_reader->buf_end - 1) & f_reader->buf_len_mask]->tp;
            front_ts = f_reader->sub_es[(f_reader->buf_end - 1) & f_reader->buf_len_mask]->ts;
        }
    }
    virtual void run_back() {
        CHECK(!q_map.empty());
        CHECK(back_tp < front_tp);

        for (size_t i = 0; i < q_map.size(); i++) {
            q_map[i].first = step(q_map[i].first, back_es());
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
        CHECK(!q_map.empty());

        b_reader->buf_beg++;
        if (b_reader->buf_end - 1 < front_tp) {
            b_reader->run();
        }
        back_tp++;
        back_ts = b_reader->sub_es[b_reader->buf_beg & b_reader->buf_len_mask]->ts;

        if (init_found) return;

        // current state is not in q_map
        int cur_tp = back_tp;
        cur.q = dfa->init;
        cur.last_sat = {};

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

            const Event *cur_es;
            timestamp cur_ts;
            if (cur_tp < b_reader->buf_end - 1) {
                cur_es = b_reader->sub_es[cur_tp & b_reader->buf_len_mask];
                cur_ts = b_reader->sub_es[cur_tp & b_reader->buf_len_mask]->ts;
            } else {
                if (c_reader == NULL) {
                    CHECK(cur_tp == b_reader->buf_end - 1);
                    c_reader = new LastReader(b_reader);
                }
                cur_es = c_reader->sub_es[cur_tp & c_reader->buf_len_mask];
                cur_ts = c_reader->sub_es[cur_tp & c_reader->buf_len_mask]->ts;
            }

            for (size_t i = 0; i < q_map.size(); i++) {
                q_map[i].second.q = step(q_map[i].second.q, cur_es);
            }

            if (acc(cur.q, cur_es)) cur.last_sat = std::make_pair(cur_ts, cur_tp);
            cur.q = step(cur.q, cur_es);

            if (cur_tp >= b_reader->buf_end - 1) {
                c_reader->run();
            }
            cur_tp++;
        }
        if (c_reader != NULL) delete c_reader;

        q_map_init = q_map.size();
        q_map.push_back(std::make_pair(dfa->init, QMapEntry(cur.last_sat, cur.q)));
    }
};

class MH_BW : public MH_FW {
    // earliest matching suffix (for BwMonitor)
    std::vector<std::pair<DState *, std::pair<timestamp, int> > > e_map;

    void e_map_add(DState *s, std::pair<timestamp, int> tsp) {
        for (size_t i = 0; i < e_map.size(); i++) {
            if (e_map[i].first == s) {
                if (e_map[i].second.second < tsp.second) e_map[i].second = tsp;
                return;
            }
        }
        e_map.push_back(std::make_pair(s, tsp));
    }

    MH_BW(MH_BW *s) : MH_FW(s), e_map(s->e_map) {}

public:
    MH_BW(DFA *dfa, LastReader *l_reader) : MH_FW(dfa, l_reader) {}
    virtual MH_BW *clone() override {
        return new MH_BW(this);
    }
    BooleanVerdict check_bw(timestamp from, timestamp to) {
        assert(!front_eof());
        timestamp t = front_ts;
        Boolean b = FALSE;
        while (back_tp < front_tp && front_ts - back_ts >= from) run_back();
        if (b_reader->unresolved || (f_reader && f_reader->unresolved)) unresolved = 1;
        if (from == 0 && acc(dfa->init, front_es())) b = TRUE;
        for (size_t i = 0; b == FALSE && i < e_map.size(); i++) {
            if (acc(e_map[i].first, front_es()) && front_ts - e_map[i].second.first <= to) b = TRUE;
        }
        run_front();
        if (unresolved) b = UNRESOLVED;
        return BooleanVerdict(t, b);
    }
    BooleanVerdict check_bw_shift(timestamp delta) {
        assert(!front_eof());
        timestamp t = front_ts;
        Boolean b = UNRESOLVED;
        while (back_tp < front_tp && front_ts - back_ts > delta) run_back();
        if (back_tp < front_tp) {
            b = check_init_tp();
        } else {
            if (acc(dfa->init, front_es())) b = TRUE;
            else b = FALSE;
        }
        if (b_reader->unresolved || (f_reader && f_reader->unresolved)) unresolved = 1;
        run_front();
        if (unresolved) b = UNRESOLVED;
        return BooleanVerdict(t, b);
    }
    virtual void run_front() override {
        CHECK(!q_map.empty());
        CHECK(!front_eof());

        const Event *cur_front_es = front_es();

        size_t idx = 0;
        for (size_t i = 0; i < e_map.size(); i++) {
            e_map[i].first = step(e_map[i].first, cur_front_es);
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
        CHECK(back_tp < front_tp);

        e_map_add(q_map[q_map_init].second.end_q, std::pair(back_ts, back_tp));
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

class BwOneMonitor : public Monitor {
    timestamp delta;
    DFA *dfa;
    int dfa_owner;

    MH_BW *s;

public:
    BwOneMonitor(timestamp delta, DFA *dfa, MH_BW *s, int dfa_owner = 1) : delta(delta), dfa(dfa), dfa_owner(dfa_owner), s(s) {}
    ~BwOneMonitor() {
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

class FwOneMonitor : public Monitor {
    timestamp delta;
    DFA *dfa;
    int dfa_owner;

    MH_FW *s;

public:
    FwOneMonitor(timestamp delta, DFA *dfa, MH_FW *s, int dfa_owner = 1) : delta(delta), dfa(dfa), dfa_owner(dfa_owner), s(s) {}
    ~FwOneMonitor() {
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
    std::optional<timestamp> t;

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

class ImpMonitor : public Monitor {
    Monitor *subf, *subg;

public:
    ImpMonitor(Monitor *subf, Monitor *subg) : subf(subf), subg(subg) {}
    ~ImpMonitor() {
        delete subf;
        delete subg;
    }
    Monitor *clone() override {
        return new ImpMonitor(subf->clone(), subg->clone());
    }
    BooleanVerdict step_impl() override {
        return subf->step().imp(subg->step());
    }
};

class EqMonitor : public Monitor {
    Monitor *subf, *subg;

public:
    EqMonitor(Monitor *subf, Monitor *subg) : subf(subf), subg(subg) {}
    ~EqMonitor() {
        delete subf;
        delete subg;
    }
    Monitor *clone() override {
        return new EqMonitor(subf->clone(), subg->clone());
    }
    BooleanVerdict step_impl() override {
        return subf->step().eq(subg->step());
    }
};

class PrevMonitor : public Monitor {
    timestamp from, to;
    Monitor *subf;
    std::optional<BooleanVerdict> v;

public:
    PrevMonitor(Monitor *subf, timestamp from, timestamp to) : from(from), to(to), subf(subf) {}
    ~PrevMonitor() {
        delete subf;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

class NextMonitor : public Monitor {
    timestamp from, to;
    Monitor *subf;
    std::optional<timestamp> t;

public:
    NextMonitor(Monitor *subf, timestamp from, timestamp to) : from(from), to(to), subf(subf) {}
    ~NextMonitor() {
        delete subf;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

struct HeadPos {
    timestamp ts;
    int tp = -1;
    int eof = 0;

    void update(timestamp new_ts) {
        ts = new_ts;
        tp++;
    }
};

class SinceMonitor : public Monitor {
    timestamp from, to;
    Monitor *subf, *subg;

    std::optional<BooleanVerdict> subfv, subgv;
    HeadPos subfp, subgp;
    int unresolved = 0;

    std::optional<std::pair<timestamp, int> > last_sat;
    std::optional<std::pair<timestamp, int> > last_viol;

public:
    SinceMonitor(Monitor *subf, Monitor *subg, timestamp from, timestamp to) : from(from), to(to), subf(subf), subg(subg) {}
    ~SinceMonitor() {
        delete subf;
        delete subg;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

class UntilMonitor : public Monitor {
    timestamp from, to;
    Monitor *subf, *subg, *subh;

    std::optional<BooleanVerdict> subfv, subgv, subhv;
    HeadPos subfp, subgp, subhp;
    int unresolved = 0;

    std::optional<std::pair<timestamp, int> > last_sat;
    std::optional<std::pair<timestamp, int> > last_viol;

    void read_fg() {
        CHECK(subfp.tp == -1 || subfp.ts == subgp.ts);
        CHECK(subfp.tp == subgp.tp);
        try {
            subfv = subf->step();
            subfp.update(subfv->ts);
            subgv = subg->step();
            subgp.update(subgv->ts);
        } catch(const EOL &e) {
            CHECK(!subfp.eof && !subgp.eof);
            subfp.tp++;
            subfp.eof = 1;
            subgp.tp++;
            subgp.eof = 1;
        }
    }

public:
    UntilMonitor(Monitor *subf, Monitor *subg, Monitor *subh, timestamp from, timestamp to) : from(from), to(to), subf(subf), subg(subg), subh(subh) {}
    ~UntilMonitor() {
        delete subf;
        delete subg;
        delete subh;
    }
    Monitor *clone() override;
    BooleanVerdict step_impl() override;
};

#endif /* __MONITOR_H__ */
