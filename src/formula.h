#ifndef __FORMULA_H__
#define __FORMULA_H__

#include "constants.h"
#include "common.h"
#include "DFA.h"
#include "util.h"

#include <cassert>
#include <cstdlib>

struct Regex;
struct LookaheadRegex;
struct SymbolRegex;
struct PlusRegex;
struct TimesRegex;
struct StarRegex;

struct Formula;
struct BoolFormula;
struct AtomFormula;
struct NegFormula;
struct AndFormula;
struct OrFormula;
struct PrevFormula;
struct NextFormula;
struct SinceFormula;
struct UntilFormula;
struct BwFormula;
struct FwFormula;

class RegexVisitor {
public:
    virtual void visit(LookaheadRegex *r) = 0;
    virtual void visit(SymbolRegex *r) = 0;
    virtual void visit(PlusRegex *r) = 0;
    virtual void visit(TimesRegex *r) = 0;
    virtual void visit(StarRegex *r) = 0;
};

class FormulaVisitor {
public:
    virtual void visit(BoolFormula *f) = 0;
    virtual void visit(AtomFormula *f) = 0;
    virtual void visit(NegFormula *f) = 0;
    virtual void visit(AndFormula *f) = 0;
    virtual void visit(OrFormula *f) = 0;
    virtual void visit(PrevFormula *f) = 0;
    virtual void visit(NextFormula *f) = 0;
    virtual void visit(SinceFormula *f) = 0;
    virtual void visit(UntilFormula *f) = 0;
    virtual void visit(BwFormula *f) = 0;
    virtual void visit(FwFormula *f) = 0;
};

struct Regex {
    virtual ~Regex() {}
    virtual void accept(RegexVisitor &v) = 0;

    virtual bool nullable() const = 0;
    virtual bool wf() const = 0;

    virtual bool equal(const Regex *r) const = 0;
    virtual bool equalLookahead(const LookaheadRegex *r) const {
        return false;
    }
    virtual bool equalSymbol(const SymbolRegex *r) const {
        return false;
    }
    virtual bool equalPlus(const PlusRegex *r) const {
        return false;
    }
    virtual bool equalTimes(const TimesRegex *r) const {
        return false;
    }
    virtual bool equalStar(const StarRegex *r) const {
        return false;
    }
};

struct LookaheadRegex : Regex {
    Formula *f;
    int f_owner;
    int fid;

    LookaheadRegex(Formula *f) : f(f), f_owner(1), fid(-1) {}
    ~LookaheadRegex();
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool nullable() const override {
        return true;
    }
    bool wf() const override {
        return false;
    }

    bool equal(const Regex *r) const override {
        return r->equalLookahead(this);
    }
    bool equalLookahead(const LookaheadRegex *r) const override;
};

struct SymbolRegex : Regex {
    Formula *f;
    int f_owner;
    int fid;

    SymbolRegex(Formula *f) : f(f), f_owner(1), fid(-1) {}
    ~SymbolRegex();
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool nullable() const override {
        return false;
    }
    bool wf() const override {
        return true;
    }

    bool equal(const Regex *r) const override {
        return r->equalSymbol(this);
    }
    bool equalSymbol(const SymbolRegex *r) const override;
};

struct PlusRegex : Regex {
    Regex *left, *right;

    PlusRegex(Regex *left, Regex *right) : left(left), right(right) {}
    ~PlusRegex() {
        if (left != NULL) delete left;
        if (right != NULL) delete right;
    }
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool nullable() const override {
        return left->nullable() || right->nullable();
    }
    bool wf() const override {
        return left->wf() && right->wf();
    }

    bool equal(const Regex *r) const override {
        return r->equalPlus(this);
    }
    bool equalPlus(const PlusRegex *r) const override {
        return left->equal(r->left) && right->equal(r->right);
    }
};

struct TimesRegex : Regex {
    Regex *left, *right;

    TimesRegex(Regex *left, Regex *right) : left(left), right(right) {}
    ~TimesRegex() {
        if (left != NULL) delete left;
        if (right != NULL) delete right;
    }
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool nullable() const override {
        return left->nullable() && right->nullable();
    }
    bool wf() const override {
        return right->wf() && (!right->nullable() || left->wf());
    }

    bool equal(const Regex *r) const override {
        return r->equalTimes(this);
    }
    bool equalTimes(const TimesRegex *r) const override {
        return left->equal(r->left) && right->equal(r->right);
    }
};

struct StarRegex : Regex {
    Regex *body;

    StarRegex(Regex *body) : body(body) {}
    ~StarRegex() {
        if (body != NULL) delete body;
    }
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool nullable() const override {
        return true;
    }
    bool wf() const override {
        return body->wf();
    }

    bool equal(const Regex *r) const override {
        return r->equalStar(this);
    }
    bool equalStar(const StarRegex *r) const override {
        return body->equal(r->body);
    }
};

struct Formula {
    int is_temporal;

    Formula(int is_temporal = 1) : is_temporal(is_temporal) {}
    virtual ~Formula() {}
    virtual bool eval(const Event *e) const {
        assert(0);
    }
    virtual void accept(FormulaVisitor &v) = 0;

    virtual bool equal(const Formula *f) const = 0;
    virtual bool equalBool(const BoolFormula *f) const {
        return false;
    }
    virtual bool equalAtom(const AtomFormula *f) const {
        return false;
    }
    virtual bool equalNeg(const NegFormula *f) const {
        return false;
    }
    virtual bool equalAnd(const AndFormula *f) const {
        return false;
    }
    virtual bool equalOr(const OrFormula *f) const {
        return false;
    }
    virtual bool equalPrev(const PrevFormula *f) const {
        return false;
    }
    virtual bool equalNext(const NextFormula *f) const {
        return false;
    }
    virtual bool equalSince(const SinceFormula *f) const {
        return false;
    }
    virtual bool equalUntil(const UntilFormula *f) const {
        return false;
    }
    virtual bool equalBw(const BwFormula *f) const {
        return false;
    }
    virtual bool equalFw(const FwFormula *f) const {
        return false;
    }
};

struct BoolFormula : Formula {
    bool b;

    BoolFormula(bool b) : Formula(0), b(b) {}
    bool eval(const Event *e) const override {
        return b;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalBool(this);
    }
    bool equalBool(const BoolFormula *f) const override {
        return b == f->b;
    }
};

struct AtomFormula : Formula {
    const char *pred_name;
    int pred;
    int pred_owner;

    AtomFormula(const char *pred_name, int pred, int pred_owner = 0) : Formula(0), pred_name(pred_name), pred(pred), pred_owner(pred_owner) {}
    ~AtomFormula() {
        if (pred_owner) delete [] pred_name;
    }
    bool eval(const Event *e) const override {
        return e->evalAtom(pred_name, pred);
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalAtom(this);
    }
    bool equalAtom(const AtomFormula *f) const override {
        return pred == f->pred;
    }
};

struct NegFormula : Formula {
    Formula *f;

    NegFormula(Formula *f) : Formula(f->is_temporal), f(f) {}
    ~NegFormula() override {
        if (f != NULL) delete f;
    }
    bool eval(const Event *e) const override {
        return !f->eval(e);
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalNeg(this);
    }
    bool equalNeg(const NegFormula *sub) const override {
        return f->equal(sub->f);
    }
};

struct AndFormula : Formula {
    Formula *f, *g;

    AndFormula(Formula *f, Formula *g) : Formula(f->is_temporal || g->is_temporal), f(f), g(g) {}
    ~AndFormula() override {
        if (f != NULL) delete f;
        if (g != NULL) delete g;
    }
    bool eval(const Event *e) const override {
        return f->eval(e) && g->eval(e);
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalAnd(this);
    }
    bool equalAnd(const AndFormula *sub) const override {
        return f->equal(sub->f) && g->equal(sub->g);
    }
};

struct OrFormula : Formula {
    Formula *f, *g;

    OrFormula(Formula *f, Formula *g) : Formula(f->is_temporal || g->is_temporal), f(f), g(g) {}
    ~OrFormula() override {
        if (f != NULL) delete f;
        if (g != NULL) delete g;
    }
    bool eval(const Event *e) const override {
        return f->eval(e) || g->eval(e);
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalOr(this);
    }
    bool equalOr(const OrFormula *sub) const override {
        return f->equal(sub->f) && g->equal(sub->g);
    }
};

struct PrevFormula : Formula {
    Formula *f;
    timestamp from, to;

    PrevFormula(Formula *f, interval in) : f(f), from(in.from), to(in.to) {}
    ~PrevFormula() override {
        if (f != NULL) delete f;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalPrev(this);
    }
    bool equalPrev(const PrevFormula *sub) const override {
        return f->equal(sub->f) && from == sub->from && to == sub->to;
    }
};

struct NextFormula : Formula {
    Formula *f;
    timestamp from, to;

    NextFormula(Formula *f, interval in) : f(f), from(in.from), to(in.to) {}
    ~NextFormula() override {
        if (f != NULL) delete f;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalNext(this);
    }
    bool equalNext(const NextFormula *sub) const override {
        return f->equal(sub->f) && from == sub->from && to == sub->to;
    }
};

struct SinceFormula : Formula {
    Formula *f, *g;
    timestamp from, to;

    SinceFormula(Formula *f, Formula *g, interval in) : f(f), g(g), from(in.from), to(in.to) {}
    ~SinceFormula() override {
        if (f != NULL) delete f;
        if (g != NULL) delete g;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalSince(this);
    }
    bool equalSince(const SinceFormula *sub) const override {
        return f->equal(sub->f) && g->equal(sub->g) && from == sub->from && to == sub->to;
    }
};

struct UntilFormula : Formula {
    Formula *f, *g;
    timestamp from, to;

    UntilFormula(Formula *f, Formula *g, interval in) : f(f), g(g), from(in.from), to(in.to) {}
    ~UntilFormula() override {
        if (f != NULL) delete f;
        if (g != NULL) delete g;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalUntil(this);
    }
    bool equalUntil(const UntilFormula *sub) const override {
        return f->equal(sub->f) && g->equal(sub->g) && from == sub->from && to == sub->to;
    }
};

struct BwFormula : Formula {
    Regex *r;
    timestamp from, to;

    BwFormula(Regex *r, interval in) : r(r), from(in.from), to(in.to) {}
    ~BwFormula() {
        if (r != NULL) delete r;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalBw(this);
    }
    bool equalBw(const BwFormula *f) const override {
        return r->equal(f->r) && from == f->from && to == f->to;
    }
};

struct FwFormula : Formula {
    Regex *r;
    timestamp from, to;

    FwFormula(Regex *r, interval in) : r(r), from(in.from), to(in.to) {}
    ~FwFormula() {
        if (r != NULL) delete r;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalFw(this);
    }
    bool equalFw(const FwFormula *f) const override {
        return r->equal(f->r) && from == f->from && to == f->to;
    }
};

#endif /* __FORMULA_H__ */
