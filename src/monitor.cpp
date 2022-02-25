#include "monitor.h"

#include <cstdlib>
#include <cstring>
#include <exception>
#include <stdexcept>

#include "common.h"
#include "formula.h"
#include "trie.h"
#include "util.h"

Monitor *NonTempMonitor::clone() {
    NonTempMonitor *mon = new NonTempMonitor(fmla, input_reader, handle->clone());
    mon->eof = eof;
    return mon;
}
BooleanVerdict NonTempMonitor::step_impl() {
    input_reader->read_handle(handle);
    if (handle->eof) throw EOL();
    bool b = fmla->eval(handle);
    return BooleanVerdict(handle->ts, b ? TRUE : FALSE);
}

Monitor *PrevMonitor::clone() {
    PrevMonitor *mon = new PrevMonitor(input_reader, handle->clone(), subf->clone(), from, to);
    mon->eof = eof;
    mon->v = v;
    return mon;
}
BooleanVerdict PrevMonitor::step_impl() {
    input_reader->read_handle(handle);
    if (handle->eof) throw EOL();
    Boolean b = FALSE;
    if (v) {
        if (mem(v->ts, handle->ts, from, to)) b = v->b;
    }
    try {
        v = subf->step();
    } catch (const EOL &e) {
        eof = 1;
    }
    return BooleanVerdict(handle->ts, b);
}

Monitor *NextMonitor::clone() {
    NextMonitor *mon = new NextMonitor(input_reader, handle->clone(), subf->clone(), from, to);
    mon->eof = eof;
    mon->t = t;
    return mon;
}
BooleanVerdict NextMonitor::step_impl() {
    input_reader->read_handle(handle);
    if (handle->eof) throw EOL();
    if (t) {
        timestamp t0 = *t;
        t = handle->ts;
        try {
            BooleanVerdict v = subf->step();
            Boolean b = FALSE;
            if (mem(t0, handle->ts, from, to)) b = v.b;
            return BooleanVerdict(t0, b);
        } catch (const EOL &e) {
            eof = 1;
            if (mem(t0, handle->ts, from, to)) {
                throw EOL();
            } else {
                return BooleanVerdict(t0, FALSE);
            }
        }
    } else {
        subf->step();
        t = handle->ts;
        return step_impl();
    }
}

Monitor *SinceMonitor::clone() {
    SinceMonitor *mon = new SinceMonitor(input_reader, handle->clone(), subf->clone(), subg->clone(), from, to);
    mon->eof = eof;
    mon->cphi = cphi;
    mon->cpsi = cpsi;
    mon->ocpsi = ocpsi;
    mon->otpsi = otpsi;
    return mon;
}
BooleanVerdict SinceMonitor::step_impl() {
    BooleanVerdict vf = subf->step();
    if (vf.b == TRUE) cphi++;
    else cphi = 0;
    cpsi++;
    if (ocpsi) (*ocpsi)++;
    while (cpsi > 0 && memL(handle->ts, vf.ts, from, to)) {
        input_reader->read_handle(handle);
        BooleanVerdict vg = subg->step();
        if (vg.b == TRUE) {
            ocpsi = cpsi;
            otpsi = vg.ts;
        }
        cpsi--;
    }
    Boolean b = FALSE;
    if (ocpsi && (*ocpsi) - 1 <= cphi && memR((*otpsi), vf.ts, from, to)) b = TRUE;
    return BooleanVerdict(vf.ts, b);
}

Monitor *UntilMonitor::clone() {
    UntilMonitor *mon = new UntilMonitor(input_reader, front->clone(), back->clone(), subf->clone(), subg->clone(), from, to);
    mon->eof = eof;
    mon->c = c;
    mon->z = z;
    return mon;
}
BooleanVerdict UntilMonitor::step_impl() {
    input_reader->read_handle(back);
    if (back->eof) throw EOL();
    while (loopCondUntil()) {
        BooleanVerdict vf = subf->step();
        BooleanVerdict vg = subg->step();
        input_reader->read_handle(front);
        c++;
        z = make_pair(vf.ts, make_pair(vf.b, vg.b));
    }
    if (c == 0) throw EOL();
    else {
        c--;
        if (z->second.second && memL(back->ts, z->first, from, to)) return BooleanVerdict(back->ts, TRUE);
        else if (!z->second.first) return BooleanVerdict(back->ts, FALSE);
        else if (front->eof) throw EOL();
        else return BooleanVerdict(back->ts, FALSE);
    }
}

Monitor *BwMonitor::clone() {
    BwMonitor *mon = new BwMonitor(from, to, dfa, s->clone(), 0);
    mon->eof = eof;
    return mon;
}
BooleanVerdict BwMonitor::step_impl() {
    return s->check_bw(from, to);
}

Monitor *FwMonitor::clone() {
    FwMonitor *mon = new FwMonitor(from, to, dfa, s->clone(), 0);
    mon->eof = eof;
    return mon;
}
BooleanVerdict FwMonitor::step_impl() {
    return s->check_fw(from, to);
}
