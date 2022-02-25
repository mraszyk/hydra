#ifndef __VISITORS_HPP__
#define __VISITORS_HPP__

#include "formula.h"
#include "monitor.h"

template<typename MH>
std::pair<DFA *, MH *> createMH(Regex *r, InputReader *input_reader);

class MonitorVisitor : public FormulaVisitor {
    InputReader *input_reader;
    Monitor *mon;

public:
    MonitorVisitor(InputReader *input_reader) : input_reader(input_reader) {}
    Monitor *get_mon() {
        return mon;
    }
    void visit(BoolFormula *f) {
        mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
    }
    void visit(AtomFormula *f) {
        mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
    }
    void visit(NegFormula *f) {
        if (f->is_temporal) {
            f->f->accept(*this);
            Monitor *monf = mon;
            mon = new NegMonitor(monf);
        } else {
            mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
        }
    }
    void visit(AndFormula *f) {
        if (f->is_temporal) {
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
        if (f->is_temporal) {
            f->f->accept(*this);
            Monitor *monf = mon;
            f->g->accept(*this);
            Monitor *mong = mon;
            mon = new OrMonitor(monf, mong);
        } else {
            mon = new NonTempMonitor(f, input_reader, input_reader->open_handle());
        }
    }
    void visit(PrevFormula *f) {
        f->f->accept(*this);
        mon = new PrevMonitor(input_reader, input_reader->open_handle(), mon, f->from, f->to);
    }
    void visit(NextFormula *f) {
        f->f->accept(*this);
        mon = new NextMonitor(input_reader, input_reader->open_handle(), mon, f->from, f->to);
    }
    void visit(SinceFormula *f) {
        f->f->accept(*this);
        Monitor *monf = mon;
        f->g->accept(*this);
        Monitor *mong = mon;
        mon = new SinceMonitor(input_reader, input_reader->open_handle(), monf, mong, f->from, f->to);
    }
    void visit(UntilFormula *f) {
        f->f->accept(*this);
        Monitor *monf = mon;
        f->g->accept(*this);
        Monitor *mong = mon;
        mon = new UntilMonitor(input_reader, input_reader->open_handle(), input_reader->open_handle(), monf, mong, f->from, f->to);
    }
    void visit(BwFormula *f) {
        std::pair<DFA *, MH_BW *> icalp = createMH<MH_BW>(f->r, input_reader);
        mon = new BwMonitor(f->from, f->to, icalp.first, icalp.second);
    }
    void visit(FwFormula *f) {
        std::pair<DFA *, MH_FW *> icalp = createMH<MH_FW>(f->r, input_reader);
        mon = new FwMonitor(f->from, f->to, icalp.first, icalp.second);
    }
};

class CollectVisitor : public RegexVisitor {
    std::vector<Formula *> &fmla;

public:
    CollectVisitor(std::vector<Formula *> &fmla) : fmla(fmla) {}
    void visit(LookaheadRegex *r) {
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
    void visit(SymbolRegex *r) {
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
    void visit(PlusRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(TimesRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarRegex *r) {
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
    void visit(LookaheadRegex *r) {
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
    void visit(SymbolRegex *r) {
        for (int i = 0; i < fmla.size(); i++) {
            if (r->f == fmla[i]) {
                r->fid = i;
                f.start = new NState(Wild, NULL, NULL);
                f.out.clear();
                f.out.push_back(&f.start->out);
                f.start = new NState(i, f.start, NULL);
                return;
            }
        }
        CHECK(0);
    }
    void visit(PlusRegex *r) {
        r->right->accept(*this);
        Frag fr = f;
        r->left->accept(*this);
        f.start = new NState(Split, f.start, fr.start);
        f.out.insert(f.out.end(), fr.out.begin(), fr.out.end());
    }
    void visit(TimesRegex *r) {
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

class StateCount : public RegexVisitor {
    int state_cnt = 0;

public:
    int get() {
        return state_cnt;
    }

    void visit(LookaheadRegex *r) {
        state_cnt++;
    }
    void visit(SymbolRegex *r) {
        state_cnt += 2;
    }
    void visit(PlusRegex *r) {
        state_cnt++;
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(TimesRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarRegex *r) {
        state_cnt++;
        r->body->accept(*this);
    }
};

class AtomRegexVisitor : public RegexVisitor {
    std::vector<const char *> &atoms;

public:
    AtomRegexVisitor(std::vector<const char *> &atoms) : atoms(atoms) {}
    void visit(LookaheadRegex *r);
    void visit(SymbolRegex *r);
    void visit(PlusRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(TimesRegex *r) {
        r->left->accept(*this);
        r->right->accept(*this);
    }
    void visit(StarRegex *r) {
        r->body->accept(*this);
    }
};

class AtomFormulaVisitor : public FormulaVisitor {
    std::vector<const char *> &atoms;

public:
    AtomFormulaVisitor(std::vector<const char *> &atoms) : atoms(atoms) {}
    void visit(BoolFormula *f) {}
    void visit(AtomFormula *f) {
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
    void visit(BwFormula *f) {
        AtomRegexVisitor v(atoms);
        f->r->accept(v);
    }
    void visit(FwFormula *f) {
        AtomRegexVisitor v(atoms);
        f->r->accept(v);
    }
};

class PrintRegexVisitor : public RegexVisitor {
    FormulaVisitor *v;
    FILE *out;

public:
    PrintRegexVisitor(FormulaVisitor *v, FILE *out) : v(v), out(out) {}
    void visit(LookaheadRegex *r);
    void visit(SymbolRegex *r);
    void visit(PlusRegex *r) {
        fprintf(out, "(");
        r->left->accept(*this);
        fprintf(out, " + ");
        r->right->accept(*this);
        fprintf(out, ")");
    }
    void visit(TimesRegex *r) {
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

#define print_op(out, inf, name, from, to) \
  if ((to) < MAX_TIMESTAMP) {\
    fprintf((out), "%s[%d,%d]", (name), (from), (to));\
  } else {\
    fprintf((out), "%s[%d,%s]", (name), (from), (inf));\
  }

class PrintHydraFormulaVisitor : public FormulaVisitor {
    FILE *out;

public:
    PrintHydraFormulaVisitor(FILE *out) : out(out) {}
    void visit(BoolFormula *f) {
        fprintf(out, "%s", f->b ? "true" : "false");
    }
    void visit(AtomFormula *f) {
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
    void visit(PrevFormula *f) {
        fprintf(out, "(");
        print_op(out, "INFINITY", "PREV", f->from, f->to);
        fprintf(out, " ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(NextFormula *f) {
        fprintf(out, "(");
        print_op(out, "INFINITY", "NEXT", f->from, f->to);
        fprintf(out, " ");
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(SinceFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " ");
        print_op(out, "INFINITY", "SINCE", f->from, f->to);
        fprintf(out, " ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(UntilFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        fprintf(out, " ");
        print_op(out, "INFINITY", "UNTIL", f->from, f->to);
        fprintf(out, " ");
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(BwFormula *f) {
        fprintf(out, "(");
        print_op(out, "INFINITY", "◁", f->from, f->to);
        PrintRegexVisitor v(this, out);
        f->r->accept(v);
        fprintf(out, ")");
    }
    void visit(FwFormula *f) {
        fprintf(out, "(");
        print_op(out, "INFINITY", "▷", f->from, f->to);
        PrintRegexVisitor v(this, out);
        f->r->accept(v);
        fprintf(out, ")");
    }
};

class PrintReelayFormulaVisitor : public FormulaVisitor {
    FILE *out;

public:
    PrintReelayFormulaVisitor(FILE *out) : out(out) {}
    void visit(BoolFormula *f) {
        CHECK(0);
    }
    void visit(AtomFormula *f) {
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
    void visit(PrevFormula *f) {
        fprintf(out, "(");
        fprintf(out, "pre ");
        CHECK(f->from == 0 && f->to == MAX_TIMESTAMP);
        f->f->accept(*this);
        fprintf(out, ")");
    }
    void visit(NextFormula *f) {
        CHECK(0);
    }
    void visit(SinceFormula *f) {
        fprintf(out, "(");
        f->f->accept(*this);
        if (f->to < MAX_TIMESTAMP) fprintf(out, " since[%d,%d] ", f->from, f->to);
        else fprintf(out, " since[>=%d] ", f->from);
        f->g->accept(*this);
        fprintf(out, ")");
    }
    void visit(UntilFormula *f) {
        CHECK(0);
    }
    void visit(BwFormula *f) {
        CHECK(0);
    }
    void visit(FwFormula *f) {
        CHECK(0);
    }
};

void print_fmla_hydra(const char *fname, Formula *fmla);
void print_fmla_reelay(const char *fname, Formula *fmla);

#endif /* __VISITORS_HPP__ */
