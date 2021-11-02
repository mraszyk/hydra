#ifndef __VISITORS_HPP__
#define __VISITORS_HPP__

#include "formula.h"
#include "monitor.h"

template<typename MH>
std::pair<DFA *, MH *> createMH(Regex *r, InputReader *input_reader);
template<typename MH>
std::pair<DFA *, MH *> createConsumeMH(ConsumeRegex *r, InputReader *input_reader);

class MonitorVisitor : public FormulaVisitor {
    InputReader *input_reader;
    Monitor *mon;

public:
    MonitorVisitor(InputReader *input_reader) : input_reader(input_reader) {}
    Monitor *get_mon() {
        return mon;
    }
    void visit(BwFormula *f) {
        std::pair<DFA *, MH_BW *> icalp = createMH<MH_BW>(f->r, input_reader);
        mon = new BwMonitor(f->from, f->to, icalp.first, icalp.second);
    }
    void visit(BwConsumeFormula *f) {
        std::pair<DFA *, MH_BW *> icalp = createConsumeMH<MH_BW>(f->r, input_reader);
        mon = new BwMonitor(f->from, f->to, icalp.first, icalp.second);
    }
    void visit(BwOneFormula *f) {
        std::pair<DFA *, MH_BW *> icalp = createMH<MH_BW>(f->r, input_reader);
        mon = new BwOneMonitor(f->delta, icalp.first, icalp.second);
    }
    void visit(FwFormula *f) {
        std::pair<DFA *, MH_FW *> icalp = createMH<MH_FW>(f->r, input_reader);
        mon = new FwMonitor(f->from, f->to, icalp.first, icalp.second);
    }
    void visit(FwConsumeFormula *f) {
        std::pair<DFA *, MH_FW *> icalp = createConsumeMH<MH_FW>(f->r, input_reader);
        mon = new FwMonitor(f->from, f->to, icalp.first, icalp.second);
    }
    void visit(FwOneFormula *f) {
        std::pair<DFA *, MH_FW *> icalp = createMH<MH_FW>(f->r, input_reader);
        mon = new FwOneMonitor(f->delta, icalp.first, icalp.second);
    }
    void visit(BoolFormula *f) {
        mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
    }
    void visit(PredFormula *f) {
        mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
    }
    void visit(NegFormula *f) {
        if (f->f->is_temporal) {
            f->f->accept(*this);
            Monitor *monf = mon;
            mon = new NegMonitor(monf);
        } else {
            mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
        }
    }
    void visit(AndFormula *f) {
        if (f->f->is_temporal || f->g->is_temporal) {
            f->f->accept(*this);
            Monitor *monf = mon;
            f->g->accept(*this);
            Monitor *mong = mon;
            mon = new AndMonitor(monf, mong);
        } else {
            mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
        }
    }
    void visit(OrFormula *f) {
        if (f->f->is_temporal || f->g->is_temporal) {
            f->f->accept(*this);
            Monitor *monf = mon;
            f->g->accept(*this);
            Monitor *mong = mon;
            mon = new OrMonitor(monf, mong);
        } else {
            mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
        }
    }
    void visit(ImpFormula *f) {
        if (f->f->is_temporal || f->g->is_temporal) {
            f->f->accept(*this);
            Monitor *monf = mon;
            f->g->accept(*this);
            Monitor *mong = mon;
            mon = new ImpMonitor(monf, mong);
        } else {
            mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
        }
    }
    void visit(EqFormula *f) {
        if (f->f->is_temporal || f->g->is_temporal) {
            f->f->accept(*this);
            Monitor *monf = mon;
            f->g->accept(*this);
            Monitor *mong = mon;
            mon = new EqMonitor(monf, mong);
        } else {
            mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
        }
    }
    void visit(PrevFormula *f) {
        f->f->accept(*this);
        mon = new PrevMonitor(mon, f->from, f->to);
    }
    void visit(NextFormula *f) {
        f->f->accept(*this);
        mon = new NextMonitor(mon, f->from, f->to);
    }
    void visit(SinceFormula *f) {
        f->f->accept(*this);
        Monitor *monf = mon;
        f->g->accept(*this);
        Monitor *mong = mon;
        mon = new SinceMonitor(monf, mong, f->from, f->to);
    }
    void visit(UntilFormula *f) {
        f->f->accept(*this);
        Monitor *monf = mon;
        f->g->accept(*this);
        Monitor *mong = mon;
        Monitor *monh = new NonTempMonitor(new BoolFormula(true), input_reader, input_reader->open_handle(), 1);
        mon = new UntilMonitor(monf, mong, monh, f->from, f->to);
    }
};

class NullableConsumeVisitor : public ConsumeRegexVisitor {
    int is_nullable;

public:
    int nullable() {
        return is_nullable;
    }

    void visit(AtomicConsumeRegex *r) {
        is_nullable = 0;
    }
    void visit(OrConsumeRegex *r) {
        r->left->accept(*this);
        if (is_nullable) return;
        r->right->accept(*this);
    }
    void visit(ConcatConsumeRegex *r) {
        r->left->accept(*this);
        if (!is_nullable) return;
        r->right->accept(*this);
    }
    void visit(StarConsumeRegex *r) {
        is_nullable = 1;
    }
};

class StateCount : public RegexVisitor {
    int state_cnt = 0;

public:
    int get() {
        return state_cnt;
    }

    void visit(TestRegex *r) {
        state_cnt++;
    }
    void visit(WildCardRegex *r) {
        state_cnt++;
    }
    void visit(OrRegex *r) {
        state_cnt++;
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(ConcatRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarRegex *r) {
        state_cnt++;
        r->body->accept(*this);
    }
};

class ConsumeStateCount : public ConsumeRegexVisitor {
    int state_cnt = 0;

public:
    int get() {
        return state_cnt;
    }

    void visit(AtomicConsumeRegex *r) {
        state_cnt++;
    }
    void visit(OrConsumeRegex *r) {
        state_cnt++;
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(ConcatConsumeRegex *r) {
        state_cnt++;
        NullableConsumeVisitor nv;
        r->left->accept(nv);
        if (nv.nullable()) state_cnt++;
        r->right->accept(nv);
        if (nv.nullable()) state_cnt++;
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarConsumeRegex *r) {
        state_cnt += 2;
        r->body->accept(*this);
    }
};

class CollectVisitor : public RegexVisitor {
    std::vector<Formula *> &fmla;

public:
    CollectVisitor(std::vector<Formula *> &fmla) : fmla(fmla) {}
    void visit(TestRegex *r) {
        for (int i = 0; i < fmla.size(); i++) {
            if (r->f->equal(fmla[i])) {
                if (r->f_owner) delete r->f;
                r->f = fmla[i];
                r->f_owner = 0;
                return;
            }
        }
        fmla.push_back(r->f);
    }
    void visit(WildCardRegex *r) {}
    void visit(OrRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(ConcatRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarRegex *r) {
        r->body->accept(*this);
    }
};

class CollectConsumeVisitor : public ConsumeRegexVisitor {
    std::vector<Formula *> &fmla;

public:
    CollectConsumeVisitor(std::vector<Formula *> &fmla) : fmla(fmla) {}
    void visit(AtomicConsumeRegex *r) {
        for (int i = 0; i < fmla.size(); i++) {
            if (r->f->equal(fmla[i])) {
                if (r->f_owner) delete r->f;
                r->f = fmla[i];
                r->f_owner = 0;
                return;
            }
        }
        fmla.push_back(r->f);
    }
    void visit(OrConsumeRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(ConcatConsumeRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarConsumeRegex *r) {
        r->body->accept(*this);
    }
};

class FragVisitor : public RegexVisitor {
    const std::vector<Formula *> &fmla;
    Frag f;

public:
    FragVisitor(const std::vector<Formula *> &fmla) : fmla(fmla) {}
    Frag get() {
        return f;
    }
    void visit(TestRegex *r) {
        for (int i = 0; i < fmla.size(); i++) {
            if (r->f == fmla[i]) {
                r->fid = i;
                f.start = new NState(i, NULL, NULL);
                f.out.clear();
                f.out.push_back(&f.start->out);
                return;
            }
        }
        CHECK(0);
    }
    void visit(WildCardRegex *r) {
        f.start = new NState(Wild, NULL, NULL);
        f.out.clear();
        f.out.push_back(&f.start->out);
    }
    void visit(OrRegex *r) {
        r->right->accept(*this);
        Frag fr = f;
        r->left->accept(*this);
        f.start = new NState(Split, f.start, fr.start);
        f.out.insert(f.out.end(), fr.out.begin(), fr.out.end());
    }
    void visit(ConcatRegex *r) {
        r->right->accept(*this);
        Frag fr = f;
        r->left->accept(*this);
        patch(f, fr.start);
        f.out = fr.out;
    }
    void visit(StarRegex *r) {
        r->body->accept(*this);
        f.start = new NState(Split, f.start, NULL);
        patch(f, f.start);
        f.out.clear();
        f.out.push_back(&f.start->out1);
    }
};

class FragConsumeVisitor : public ConsumeRegexVisitor {
    const std::vector<Formula *> &fmla;
    Frag f;

public:
    FragConsumeVisitor(const std::vector<Formula *> &fmla) : fmla(fmla) {}
    void nullate() {
        f.start = new NState(Split, f.start, NULL);
        f.out.push_back(&f.start->out1);
    }
    Frag get() {
        return f;
    }
    void visit(AtomicConsumeRegex *r) {
        for (int i = 0; i < fmla.size(); i++) {
            if (r->f == fmla[i]) {
                r->fid = i;
                f.start = new NState(i, NULL, NULL);
                f.out.clear();
                f.out.push_back(&f.start->out);
                return;
            }
        }
        CHECK(0);
    }
    void visit(OrConsumeRegex *r) {
        r->right->accept(*this);
        Frag fr = f;
        r->left->accept(*this);
        f.start = new NState(Split, f.start, fr.start);
        f.out.insert(f.out.end(), fr.out.begin(), fr.out.end());
    }
    void visit(ConcatConsumeRegex *r) {
        r->left->accept(*this);
        Frag fl = f;
        r->right->accept(*this);
        Frag fr = f;
        NState *wild_state = new NState(Wild, fr.start, NULL);
        NState *l_split, *r_split;
        NullableConsumeVisitor nv;
        r->left->accept(nv);
        if (nv.nullable()) {
            l_split = new NState(Split, fl.start, fr.start);
        } else {
            l_split = fl.start;
        }
        r->right->accept(nv);
        if (nv.nullable()) {
            r_split = new NState(Split, wild_state, NULL);
            f.out.push_back(&r_split->out1);
        } else {
            r_split = wild_state;
        }
        patch(fl, r_split);
        f.start = l_split;
    }
    void visit(StarConsumeRegex *r) {
        r->body->accept(*this);
        NState *body_start = f.start;
        NState *wild_state = new NState(Wild, body_start, NULL);
        NState *past_split = new NState(Split, wild_state, NULL);
        patch(f, past_split);
        f.start = body_start;
        f.out.clear();
        f.out.push_back(&past_split->out1);
    }
};

class AtomRegexVisitor : public RegexVisitor {
    std::vector<const char *> &atoms;

public:
    AtomRegexVisitor(std::vector<const char *> &atoms) : atoms(atoms) {}
    void visit(TestRegex *r);
    void visit(WildCardRegex *r) {}
    void visit(OrRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(ConcatRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarRegex *r) {
        r->body->accept(*this);
    }
};

class AtomConsumeRegexVisitor : public ConsumeRegexVisitor {
    std::vector<const char *> &atoms;

public:
    AtomConsumeRegexVisitor(std::vector<const char *> &atoms) : atoms(atoms) {}
    void visit(AtomicConsumeRegex *r);
    void visit(OrConsumeRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(ConcatConsumeRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarConsumeRegex *r) {
        r->body->accept(*this);
    }
};

class AtomFormulaVisitor : public FormulaVisitor {
    std::vector<const char *> &atoms;

public:
    AtomFormulaVisitor(std::vector<const char *> &atoms) : atoms(atoms) {}
    void visit(BwFormula *f) {
        AtomRegexVisitor v(atoms);
        f->r->accept(v);
    }
    void visit(BwConsumeFormula *f) {
        AtomConsumeRegexVisitor v(atoms);
        f->r->accept(v);
    }
    void visit(BwOneFormula *f) {
        AtomRegexVisitor v(atoms);
        f->r->accept(v);
    }
    void visit(FwFormula *f) {
        AtomRegexVisitor v(atoms);
        f->r->accept(v);
    }
    void visit(FwConsumeFormula *f) {
        AtomConsumeRegexVisitor v(atoms);
        f->r->accept(v);
    }
    void visit(FwOneFormula *f) {
        AtomRegexVisitor v(atoms);
        f->r->accept(v);
    }
    void visit(BoolFormula *f) {}
    void visit(PredFormula *f) {
        for (size_t i = 0; i < atoms.size(); i++) {
            if (!strcmp(atoms[i], f->pred_name)) return;
        }
        atoms.push_back(f->pred_name);
    }
    void visit(NegFormula *f) {
        f->f->accept(*this);
    }
    void visit(AndFormula *f) {
        f->f->accept(*this);
        f->g->accept(*this);
    }
    void visit(OrFormula *f) {
        f->f->accept(*this);
        f->g->accept(*this);
    }
    void visit(ImpFormula *f) {
        f->f->accept(*this);
        f->g->accept(*this);
    }
    void visit(EqFormula *f) {
        f->f->accept(*this);
        f->g->accept(*this);
    }
    void visit(PrevFormula *f) {
        f->f->accept(*this);
    }
    void visit(NextFormula *f) {
        f->f->accept(*this);
    }
    void visit(SinceFormula *f) {
        f->f->accept(*this);
        f->g->accept(*this);
    }
    void visit(UntilFormula *f) {
        f->f->accept(*this);
        f->g->accept(*this);
    }
};

class PrintHydraRegexVisitor : public RegexVisitor {
    FILE *out;

public:
    PrintHydraRegexVisitor(FILE *out) : out(out) {}
    void visit(TestRegex *r);
    void visit(WildCardRegex *r) {
        fprintf(out, ".");
    }
    void visit(OrRegex *r) {
        fprintf(out, "(");
        r->left->accept(*this);
        fprintf(out, " + ");
        r->right->accept(*this);
        fprintf(out, ")");
    }
    void visit(ConcatRegex *r) {
        fprintf(out, "(");
        r->left->accept(*this);
        fprintf(out, " ");
        r->right->accept(*this);
        fprintf(out, ")");
    }
    void visit(StarRegex *r) {
        fprintf(out, "(");
        r->body->accept(*this);
        fprintf(out, "*)");
    }
};

class PrintMonpolyRegexVisitor : public RegexVisitor {
    FILE *out;

public:
    PrintMonpolyRegexVisitor(FILE *out) : out(out) {}
    void visit(TestRegex *r);
    void visit(WildCardRegex *r) {
        fprintf(out, ".");
    }
    void visit(OrRegex *r) {
        fprintf(out, "(");
        r->left->accept(*this);
        fprintf(out, " + ");
        r->right->accept(*this);
        fprintf(out, ")");
    }
    void visit(ConcatRegex *r) {
        fprintf(out, "(");
        r->left->accept(*this);
        fprintf(out, " ");
        r->right->accept(*this);
        fprintf(out, ")");
    }
    void visit(StarRegex *r) {
        fprintf(out, "(");
        r->body->accept(*this);
        fprintf(out, "*)");
    }
};

class PrintConsumeRegexVisitor : public ConsumeRegexVisitor {
    FILE *out;

public:
    PrintConsumeRegexVisitor(FILE *out) : out(out) {}
    void visit(AtomicConsumeRegex *r);
    void visit(OrConsumeRegex *r) {
        fprintf(out, "(");
        r->left->accept(*this);
        fprintf(out, "|");
        r->right->accept(*this);
        fprintf(out, ")");
    }
    void visit(ConcatConsumeRegex *r) {
        fprintf(out, "(");
        r->left->accept(*this);
        fprintf(out, ";");
        r->right->accept(*this);
        fprintf(out, ")");
    }
    void visit(StarConsumeRegex *r) {
        fprintf(out, "(");
        r->body->accept(*this);
        fprintf(out, "*)");
    }
};

class PrintHydraFormulaVisitor : public FormulaVisitor {
    FILE *out;

public:
    PrintHydraFormulaVisitor(FILE *out) : out(out) {}
    void visit(BwFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "◁ [%d,%d] ", f->from, f->to);
        else fprintf(out, "◁ [%d,INFINITY] ", f->from);
        PrintHydraRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(BwConsumeFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "◁r [%d,%d] ", f->from, f->to);
        else fprintf(out, "◁r [%d,INFINITY] ", f->from);
        PrintConsumeRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(BwOneFormula *f) {
        fprintf(out, "(");
        fprintf(out, "◁ %d ", f->delta);
        PrintHydraRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(FwFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "▷ [%d,%d] ", f->from, f->to);
        else fprintf(out, "▷ [%d,INFINITY] ", f->from);
        PrintHydraRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(FwConsumeFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "▷r [%d,%d] ", f->from, f->to);
        else fprintf(out, "▷r [%d,INFINITY] ", f->from);
        PrintConsumeRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(FwOneFormula *f) {
        fprintf(out, "(");
        fprintf(out, "▷ %d ", f->delta);
        PrintHydraRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(BoolFormula *f) {
        fprintf(out, "%s", f->b ? "true" : "false");
    }
    void visit(PredFormula *f) {
        fprintf(out, "%s", f->pred_name);
    }
    void visit(NegFormula *f) {
        fprintf(out, "(");
        fprintf(out, "NOT ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(AndFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " AND ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(OrFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " OR ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(ImpFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " -> ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(EqFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " <-> ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(PrevFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "PREV[%d,%d] ", f->from, f->to);
        else fprintf(out, "PREV[%d,INFINITY] ", f->from);
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(NextFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "NEXT[%d,%d] ", f->from, f->to);
        else fprintf(out, "NEXT[%d,INFINITY] ", f->from);
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(SinceFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        if (f->to < MAX_TIMESTAMP) fprintf(out, " SINCE[%d,%d] ", f->from, f->to);
        else fprintf(out, " SINCE[%d,INFINITY] ", f->from);
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(UntilFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        if (f->to < MAX_TIMESTAMP) fprintf(out, " UNTIL[%d,%d] ", f->from, f->to);
        else fprintf(out, " UNTIL[%d,INFINITY] ", f->from);
        f->g->accept(*this);
        fprintf(out, ")");
    }
};

class PrintMonpolyFormulaVisitor : public FormulaVisitor {
    FILE *out;

public:
    PrintMonpolyFormulaVisitor(FILE *out) : out(out) {}
    void visit(BwFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "◁ [%d,%d] ", f->from, f->to);
        else fprintf(out, "◁ [%d,*) ", f->from);
        PrintMonpolyRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(BwConsumeFormula *f) {
        CHECK(0);
    }
    void visit(BwOneFormula *f) {
        fprintf(out, "(");
        fprintf(out, "◁ %d ", f->delta);
        PrintMonpolyRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(FwFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "▷ [%d,%d] ", f->from, f->to);
        else fprintf(out, "▷ [%d,*) ", f->from);
        PrintMonpolyRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(FwConsumeFormula *f) {
        CHECK(0);
    }
    void visit(FwOneFormula *f) {
        fprintf(out, "(");
        fprintf(out, "▷ %d ", f->delta);
        PrintMonpolyRegexVisitor r(out);
        f->r->accept(r);
        fprintf(out, ")");
    }
    void visit(BoolFormula *f) {
        fprintf(out, "%s", f->b ? "TRUE" : "FALSE");
    }
    void visit(PredFormula *f) {
        fprintf(out, "%s()", f->pred_name);
    }
    void visit(NegFormula *f) {
        fprintf(out, "(");
        fprintf(out, "NOT ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(AndFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " AND ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(OrFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " OR ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(ImpFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " IMPLIES ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(EqFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " EQUIV ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(PrevFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "PREV[%d,%d] ", f->from, f->to);
        else fprintf(out, "PREV[%d,*) ", f->from);
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(NextFormula *f) {
        fprintf(out, "(");
        if (f->to < MAX_TIMESTAMP) fprintf(out, "NEXT[%d,%d] ", f->from, f->to);
        else fprintf(out, "NEXT[%d,*) ", f->from);
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(SinceFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        if (f->to < MAX_TIMESTAMP) fprintf(out, " SINCE[%d,%d] ", f->from, f->to);
        else fprintf(out, " SINCE[%d,*) ", f->from);
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(UntilFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        if (f->to < MAX_TIMESTAMP) fprintf(out, " UNTIL[%d,%d] ", f->from, f->to);
        else fprintf(out, " UNTIL[%d,*) ", f->from);
        f->g->accept(*this);
        fprintf(out, ")");
    }
};

class PrintReelayFormulaVisitor : public FormulaVisitor {
    FILE *out;

public:
    PrintReelayFormulaVisitor(FILE *out) : out(out) {}
    void visit(BwFormula *f) {
        CHECK(0);
    }
    void visit(BwConsumeFormula *f) {
        CHECK(0);
    }
    void visit(BwOneFormula *f) {
        CHECK(0);
    }
    void visit(FwFormula *f) {
        CHECK(0);
    }
    void visit(FwConsumeFormula *f) {
        CHECK(0);
    }
    void visit(FwOneFormula *f) {
        CHECK(0);
    }
    void visit(BoolFormula *f) {
        CHECK(0);
    }
    void visit(PredFormula *f) {
        fprintf(out, "%s", f->pred_name);
    }
    void visit(NegFormula *f) {
        fprintf(out, "(");
        fprintf(out, "! ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(AndFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " && ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(OrFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " || ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(ImpFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " -> ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(EqFormula *f) {
        CHECK(0);
    }
    void visit(PrevFormula *f) {
        fprintf(out, "(");
        fprintf(out, "pre ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(NextFormula *f) {
        CHECK(0);
    }
    void visit(SinceFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        if (f->from == 0) {
            if (f->to == MAX_TIMESTAMP) fprintf(out, " since ");
            else fprintf(out, " since[<=%d] ", f->to);
        } else {
            if (f->to == MAX_TIMESTAMP) fprintf(out, " since[>=%d] ", f->from);
            else fprintf(out, " since[%d,%d] ", f->from, f->to);
        }
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(UntilFormula *f) {
        CHECK(0);
    }
};

class PrintRymtlVisitor : public FormulaVisitor {
    FILE *out;

public:
    PrintRymtlVisitor(FILE *out) : out(out) {}
    void visit(BwFormula *f) {
        CHECK(0);
    }
    void visit(BwConsumeFormula *f) {
        CHECK(0);
    }
    void visit(BwOneFormula *f) {
        CHECK(0);
    }
    void visit(FwFormula *f) {
        CHECK(0);
    }
    void visit(FwConsumeFormula *f) {
        CHECK(0);
    }
    void visit(FwOneFormula *f) {
        CHECK(0);
    }
    void visit(BoolFormula *f) {
        CHECK(0);
    }
    void visit(PredFormula *f) {
        fprintf(out, "%s", f->pred_name);
    }
    void visit(NegFormula *f) {
        fprintf(out, "(");
        fprintf(out, "! ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(AndFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " && ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(OrFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " || ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(ImpFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " -> ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(EqFormula *f) {
        CHECK(0);
    }
    void visit(PrevFormula *f) {
        fprintf(out, "(");
        fprintf(out, "Y ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(NextFormula *f) {
        CHECK(0);
    }
    void visit(SinceFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        if (f->from == 0) {
            if (f->to == MAX_TIMESTAMP) fprintf(out, " S ");
            else fprintf(out, " S[:%d] ", f->to);
        } else {
            if (f->to == MAX_TIMESTAMP) fprintf(out, " S[%d:] ", f->from);
            else fprintf(out, " S[%d:%d] ", f->from, f->to);
        }
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(UntilFormula *f) {
        CHECK(0);
    }
};

class PrintR2U2Visitor : public FormulaVisitor {
    FILE *out;

public:
    PrintR2U2Visitor(FILE *out) : out(out) {}
    void visit(BwFormula *f) {
        CHECK(0);
    }
    void visit(BwConsumeFormula *f) {
        CHECK(0);
    }
    void visit(BwOneFormula *f) {
        CHECK(0);
    }
    void visit(FwFormula *f) {
        CHECK(0);
    }
    void visit(FwConsumeFormula *f) {
        CHECK(0);
    }
    void visit(FwOneFormula *f) {
        CHECK(0);
    }
    void visit(BoolFormula *f) {
        CHECK(0);
    }
    void visit(PredFormula *f) {
        fprintf(out, "(%s)", f->pred_name);
    }
    void visit(NegFormula *f) {
        fprintf(out, "(");
        fprintf(out, "! ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(AndFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " & ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(OrFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " | ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(ImpFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " -> ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(EqFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " <-> ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(PrevFormula *f) {
        fprintf(out, "(");
        CHECK(f->from == 0 && f->to == MAX_TIMESTAMP);
        fprintf(out, "O[1,1] ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(NextFormula *f) {
        fprintf(out, "(");
        CHECK(f->from == 0 && f->to == MAX_TIMESTAMP);
        fprintf(out, "F[1,1] ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(SinceFormula *f) {
        fprintf(out, "(");
        CHECK(f->to < MAX_TIMESTAMP);
        f->f->accept(*this);
        fprintf(out, " S[%d,%d] ", f->from, f->to);
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(UntilFormula *f) {
        fprintf(out, "(");
        CHECK(f->to < MAX_TIMESTAMP);
        f->f->accept(*this);
        fprintf(out, " U[%d,%d] ", f->from, f->to);
        f->g->accept(*this);
        fprintf(out, ")");
    }
};

void print_fmla_hydra(const char *fname, Formula *fmla);
void print_fmla_monpoly(const char *fname, Formula *fmla);
void print_regex_reelay(const char *fname, ConsumeRegex *r);
void print_fmla_reelay(const char *fname, Formula *fmla);
void print_fmla_rymtl(const char *fname, Formula *fmla);
void print_fmla_r2u2(const char *fname, Formula *fmla);

#endif /* __VISITORS_HPP__ */
