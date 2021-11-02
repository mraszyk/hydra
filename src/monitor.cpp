#include "monitor.h"

#include <cstdlib>
#include <cstring>
#include <exception>
#include <stdexcept>

#include "common.h"
#include "formula.h"
#include "trie.h"
#include "util.h"

#define contains(x, f, t) ((f) <= (x) && (x) <= (t))

Monitor *NonTempMonitor::clone() {
    NonTempMonitor *mon = new NonTempMonitor(fmla, input_reader, handle->clone());
    mon->eof = eof;
    mon->t = t;
    return mon;
}
BooleanVerdict NonTempMonitor::step_impl() {
    input_reader->read_handle(handle);
    if (handle->eof) throw EOL();
    bool b = fmla->eval(handle);
    return BooleanVerdict(handle->ts, b ? TRUE : FALSE);
}

Monitor *BwMonitor::clone() {
    BwMonitor *mon = new BwMonitor(from, to, dfa, s->clone(), 0);
    mon->eof = eof;
    return mon;
}
BooleanVerdict BwMonitor::step_impl() {
    BooleanVerdict v = s->check_bw(from, to);

    if (s->front_eof()) eof = 1;

    return v;
}

Monitor *BwOneMonitor::clone() {
    BwOneMonitor *mon = new BwOneMonitor(delta, dfa, s->clone(), 0);
    mon->eof = eof;
    return mon;
}
BooleanVerdict BwOneMonitor::step_impl() {
    BooleanVerdict v = s->check_bw_shift(delta);

    if (s->front_eof()) eof = 1;

    return v;
}

Monitor *FwMonitor::clone() {
    FwMonitor *mon = new FwMonitor(from, to, dfa, s->clone(), 0);
    mon->eof = eof;
    return mon;
}
BooleanVerdict FwMonitor::step_impl() {
    if (s->back_eof()) {
        eof = 1;
        throw EOL();
    }
    return s->check_fw(from, to);
}

Monitor *FwOneMonitor::clone() {
    FwOneMonitor *mon = new FwOneMonitor(delta, dfa, s->clone(), 0);
    mon->eof = eof;
    return mon;
}
BooleanVerdict FwOneMonitor::step_impl() {
    if (s->back_eof()) {
        eof = 1;
        throw EOL();
    }
    return s->check_fw_shift(delta);
}

Monitor *PrevMonitor::clone() {
    Monitor *monf = subf->clone();
    PrevMonitor *mon = new PrevMonitor(monf, from, to);
    mon->eof = eof;
    mon->v = v;
    return mon;
}
BooleanVerdict PrevMonitor::step_impl() {
    BooleanVerdict subv = subf->step();

    if (v) {
        BooleanVerdict last_subv = *v;
        v = subv;
        if (contains(subv.ts - last_subv.ts, from, to)) return BooleanVerdict(subv.ts, last_subv.b);
        else return BooleanVerdict(subv.ts, FALSE);
    } else {
        v = subv;
        return BooleanVerdict(subv.ts, FALSE);
    }
}

Monitor *NextMonitor::clone() {
    Monitor *monf = subf->clone();
    NextMonitor *mon = new NextMonitor(monf, from, to);
    mon->eof = eof;
    mon->t = t;
    return mon;
}
BooleanVerdict NextMonitor::step_impl() {
    do {
        try {
            BooleanVerdict subv = subf->step();

            if (t) {
                timestamp last_ts = *t;
                t = subv.ts;
                if (contains(subv.ts - last_ts, from, to)) return BooleanVerdict(last_ts, subv.b);
                else return BooleanVerdict(last_ts, FALSE);
            } else {
                t = subv.ts;
            }
        } catch(const EOL &e) {
            if (t) {
                timestamp ts = *t;
                t = {};
                return BooleanVerdict(ts, UNRESOLVED);
            }
            else throw EOL();
        }
    } while(true);
}

Monitor *SinceMonitor::clone() {
    Monitor *monf = subf->clone();
    Monitor *mong = subg->clone();
    SinceMonitor *mon = new SinceMonitor(monf, mong, from, to);
    mon->eof = eof;
    mon->subfv = subfv;
    mon->subgv = subgv;
    mon->subfp = subfp;
    mon->subgp = subgp;
    mon->unresolved = unresolved;
    mon->last_sat = last_sat;
    mon->last_viol = last_viol;
    return mon;
}
BooleanVerdict SinceMonitor::step_impl() {
    subfv = subf->step();
    subfp.update(subfv->ts);

    if (subfv->b == UNRESOLVED) {
        unresolved = 1;
    } else if (subfv->b == FALSE) {
        last_viol = std::make_pair(subfp.ts, subfp.tp);
    }

    if (subgp.tp == -1) {
        subgv = subg->step();
        subgp.update(subgv->ts);
    }

    while (!subgp.eof && subgp.tp <= subfp.tp && subfp.ts - subgp.ts >= from) {
        if (subgv->b == UNRESOLVED) {
            unresolved = 1;
        } else if (subgv->b == TRUE) {
            last_sat = std::make_pair(subgp.ts, subgp.tp);
        }
        try {
            subgv = subg->step();
            subgp.update(subgv->ts);
        } catch(const EOL &e) {
            subgp.eof = 1;
            subgp.tp++;
        }
    }

    if (unresolved) {
        return BooleanVerdict(subfp.ts, UNRESOLVED);
    } else {
        int v = last_sat && subfp.ts - last_sat->first <= to && (!last_viol || last_sat->second >= last_viol->second);
        return BooleanVerdict(subfp.ts, v ? TRUE : FALSE);
    }
}

Monitor *UntilMonitor::clone() {
    Monitor *monf = subf->clone();
    Monitor *mong = subg->clone();
    Monitor *monh = subh->clone();
    UntilMonitor *mon = new UntilMonitor(monf, mong, monh, from, to);
    mon->eof = eof;
    mon->subfv = subfv;
    mon->subgv = subgv;
    mon->subhv = subhv;
    mon->subfp = subfp;
    mon->subgp = subgp;
    mon->subhp = subhp;
    mon->unresolved = unresolved;
    mon->last_sat = last_sat;
    mon->last_viol = last_viol;
    return mon;
}
BooleanVerdict UntilMonitor::step_impl() {
    subhv = subh->step();
    subhp.update(subhv->ts);

    if (last_sat && last_sat->second < subhp.tp) last_sat = {};
    if (last_viol && last_viol->second < subhp.tp) last_viol = {};

    if (subfp.tp == -1) read_fg();

    while (!subfp.eof && !last_viol && subfp.ts - subhp.ts <= to) {
        if (subgv->b == UNRESOLVED) {
            unresolved = 1;
        } else if (subgv->b == TRUE) {
            last_sat = std::make_pair(subfp.ts, subfp.tp);
        }
        if (subfv->b == UNRESOLVED) {
            unresolved = 1;
        } else if (subfv->b == FALSE) {
            last_viol = std::make_pair(subfp.ts, subfp.tp);
        }
        read_fg();
    }

    if (unresolved) {
        return BooleanVerdict(subhp.ts, UNRESOLVED);
    } else {
        int v = last_sat && last_sat->first - subhp.ts >= from;
	if (v) return BooleanVerdict(subhp.ts, TRUE);
	else if (subfp.eof) return BooleanVerdict(subhp.ts, UNRESOLVED);
	else return BooleanVerdict(subhp.ts, FALSE);
    }
}
