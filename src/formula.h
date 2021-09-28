#ifndef __FORMULA_H__
#define __FORMULA_H__

#include "constants.h"
#include "common.h"
#include "DFA.h"
#include "util.h"

#include <cassert>
#include <cstdlib>

class Monitor;

struct Regex;
struct TestRegex;
struct WildCardRegex;
struct OrRegex;
struct ConcatRegex;
struct StarRegex;

struct ConsumeRegex;
struct AtomicConsumeRegex;
struct OrConsumeRegex;
struct ConcatConsumeRegex;
struct StarConsumeRegex;

struct Formula;
struct BwFormula;
struct BwConsumeFormula;
struct BwOneFormula;
struct FwFormula;
struct FwConsumeFormula;
struct FwOneFormula;
struct BoolFormula;
struct PredFormula;
struct NegFormula;
struct AndFormula;
struct OrFormula;
struct ImpFormula;
struct EqFormula;
struct PrevFormula;
struct NextFormula;
struct SinceFormula;
struct UntilFormula;

class RegexVisitor {
public:
    virtual void visit(TestRegex *r) = 0;
    virtual void visit(WildCardRegex *r) = 0;
    virtual void visit(OrRegex *r) = 0;
    virtual void visit(ConcatRegex *r) = 0;
    virtual void visit(StarRegex *r) = 0;
};

class ConsumeRegexVisitor {
public:
    virtual void visit(AtomicConsumeRegex *r) = 0;
    virtual void visit(OrConsumeRegex *r) = 0;
    virtual void visit(ConcatConsumeRegex *r) = 0;
    virtual void visit(StarConsumeRegex *r) = 0;
};

class FormulaVisitor {
public:
    virtual void visit(BwFormula *f) = 0;
    virtual void visit(BwConsumeFormula *f) = 0;
    virtual void visit(BwOneFormula *f) = 0;
    virtual void visit(FwFormula *f) = 0;
    virtual void visit(FwConsumeFormula *f) = 0;
    virtual void visit(FwOneFormula *f) = 0;
    virtual void visit(BoolFormula *f) = 0;
    virtual void visit(PredFormula *f) = 0;
    virtual void visit(NegFormula *f) = 0;
    virtual void visit(AndFormula *f) = 0;
    virtual void visit(OrFormula *f) = 0;
    virtual void visit(ImpFormula *f) = 0;
    virtual void visit(EqFormula *f) = 0;
    virtual void visit(PrevFormula *f) = 0;
    virtual void visit(NextFormula *f) = 0;
    virtual void visit(SinceFormula *f) = 0;
    virtual void visit(UntilFormula *f) = 0;
};

struct Regex {
    virtual ~Regex() {}
    virtual void accept(RegexVisitor &v) = 0;

    virtual bool equal(const Regex *r) const = 0;
    virtual bool equalTest(const TestRegex *r) const {
        return false;
    }
    virtual bool equalWildCard(const WildCardRegex *r) const {
        return false;
    }
    virtual bool equalOr(const OrRegex *r) const {
        return false;
    }
    virtual bool equalConcat(const ConcatRegex *r) const {
        return false;
    }
    virtual bool equalStar(const StarRegex *r) const {
        return false;
    }
};

struct TestRegex : Regex {
    Formula *f;
    int f_owner;
    int fid;

    TestRegex(Formula *f) : f(f), f_owner(1) {}
    ~TestRegex();
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Regex *r) const override {
        return r->equalTest(this);
    }
    bool equalTest(const TestRegex *r) const override;
};

struct WildCardRegex : Regex {
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Regex *r) const override {
        return r->equalWildCard(this);
    }
    bool equalWild(const WildCardRegex *r) {
        return true;
    }
};

struct OrRegex : Regex {
    Regex *left, *right;

    OrRegex(Regex *left, Regex *right) : left(left), right(right) {}
    ~OrRegex() {
        if (left != NULL) delete left;
        if (right != NULL) delete right;
    }
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Regex *r) const override {
        return r->equalOr(this);
    }
    bool equalOr(const OrRegex *r) const override {
        return (left->equal(r->left) && right->equal(r->right)) || (left->equal(r->right) && right->equal(r->left));
    }
};

struct ConcatRegex : Regex {
    Regex *left, *right;

    ConcatRegex(Regex *left, Regex *right) : left(left), right(right) {}
    ~ConcatRegex() {
        if (left != NULL) delete left;
        if (right != NULL) delete right;
    }
    void accept(RegexVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Regex *r) const override {
        return r->equalConcat(this);
    }
    bool equalConcat(const ConcatRegex *r) const override {
        return (left->equal(r->left) && right->equal(r->right)) || (left->equal(r->right) && right->equal(r->left));
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

    bool equal(const Regex *r) const override {
        return r->equalStar(this);
    }
    bool equalStar(const StarRegex *r) const override {
        return body->equal(r->body);
    }
};

struct ConsumeRegex {
    virtual ~ConsumeRegex() {}
    virtual void accept(ConsumeRegexVisitor &v) = 0;

    virtual bool equal(const ConsumeRegex *r) const = 0;
    virtual bool equalAtomic(const AtomicConsumeRegex *r) const {
        return false;
    }
    virtual bool equalOr(const OrConsumeRegex *r) const {
        return false;
    }
    virtual bool equalConcat(const ConcatConsumeRegex *r) const {
        return false;
    }
    virtual bool equalStar(const StarConsumeRegex *r) const {
        return false;
    }
};

struct AtomicConsumeRegex : ConsumeRegex {
    Formula *f;
    int f_owner;
    int fid;

    AtomicConsumeRegex(Formula *f) : f(f), f_owner(1) {}
    ~AtomicConsumeRegex();
    void accept(ConsumeRegexVisitor &v) override {
        v.visit(this);
    }

    bool equal(const ConsumeRegex *r) const override {
        return r->equalAtomic(this);
    }
    bool equalAtomic(const AtomicConsumeRegex *r) const override;
};

struct OrConsumeRegex : ConsumeRegex {
    ConsumeRegex *left, *right;

    OrConsumeRegex(ConsumeRegex *left, ConsumeRegex *right) : left(left), right(right) {}
    ~OrConsumeRegex() {
        if (left != NULL) delete left;
        if (right != NULL) delete right;
    }
    void accept(ConsumeRegexVisitor &v) override {
        v.visit(this);
    }

    bool equal(const ConsumeRegex *r) const override {
        return r->equalOr(this);
    }
    bool equalOr(const OrConsumeRegex *r) const override {
        return (left->equal(r->left) && right->equal(r->right)) || (left->equal(r->right) && right->equal(r->left));
    }
};

struct ConcatConsumeRegex : ConsumeRegex {
    ConsumeRegex *left, *right;

    ConcatConsumeRegex(ConsumeRegex *left, ConsumeRegex *right) : left(left), right(right) {}
    ~ConcatConsumeRegex() {
        if (left != NULL) delete left;
        if (right != NULL) delete right;
    }
    void accept(ConsumeRegexVisitor &v) override {
        v.visit(this);
    }

    bool equal(const ConsumeRegex *r) const override {
        return r->equalConcat(this);
    }
    bool equalConcat(const ConcatConsumeRegex *r) const override {
        return (left->equal(r->left) && right->equal(r->right)) || (left->equal(r->right) && right->equal(r->left));
    }
};

struct StarConsumeRegex : ConsumeRegex {
    ConsumeRegex *body;

    StarConsumeRegex(ConsumeRegex *body) : body(body) {}
    ~StarConsumeRegex() {
        if (body != NULL) delete body;
    }
    void accept(ConsumeRegexVisitor &v) override {
        v.visit(this);
    }

    bool equal(const ConsumeRegex *r) const override {
        return r->equalStar(this);
    }
    bool equalStar(const StarConsumeRegex *r) const override {
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
    virtual bool equalBw(const BwFormula *f) const {
        return false;
    }
    virtual bool equalBwConsume(const BwConsumeFormula *f) const {
        return false;
    }
    virtual bool equalBwOne(const BwOneFormula *f) const {
        return false;
    }
    virtual bool equalFw(const FwFormula *f) const {
        return false;
    }
    virtual bool equalFwConsume(const FwConsumeFormula *f) const {
        return false;
    }
    virtual bool equalFwOne(const FwOneFormula *f) const {
        return false;
    }
    virtual bool equalBool(const BoolFormula *f) const {
        return false;
    }
    virtual bool equalPred(const PredFormula *f) const {
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
    virtual bool equalImp(const ImpFormula *f) const {
        return false;
    }
    virtual bool equalEq(const EqFormula *f) const {
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

struct BwConsumeFormula : Formula {
    ConsumeRegex *r;
    timestamp from, to;

    BwConsumeFormula(ConsumeRegex *r, interval in) : r(r), from(in.from), to(in.to) {}
    ~BwConsumeFormula() {
        if (r != NULL) delete r;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalBwConsume(this);
    }
    bool equalBwConsume(const BwConsumeFormula *f) const override {
        return r->equal(f->r) && from == f->from && to == f->to;
    }
};

struct BwOneFormula : Formula {
    Regex *r;
    timestamp delta;

    BwOneFormula(Regex *r, timestamp delta) : r(r), delta(delta) {}
    ~BwOneFormula() {
        if (r != NULL) delete r;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalBwOne(this);
    }
    bool equalBwOne(const BwOneFormula *f) const override {
        return r->equal(f->r) && delta == f->delta;
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

struct FwConsumeFormula : Formula {
    ConsumeRegex *r;
    timestamp from, to;

    FwConsumeFormula(ConsumeRegex *r, interval in) : r(r), from(in.from), to(in.to) {}
    ~FwConsumeFormula() {
        if (r != NULL) delete r;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalFwConsume(this);
    }
    bool equalFwConsume(const FwConsumeFormula *f) const override {
        return r->equal(f->r) && from == f->from && to == f->to;
    }
};

struct FwOneFormula : Formula {
    Regex *r;
    timestamp delta;

    FwOneFormula(Regex *r, timestamp delta) : r(r), delta(delta) {}
    ~FwOneFormula() {
        if (r != NULL) delete r;
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalFwOne(this);
    }
    bool equalFwOne(const FwOneFormula *f) const override {
        return r->equal(f->r) && delta == f->delta;
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

struct PredFormula : Formula {
    const char *pred_name;
    int pred;
    int pred_owner;

    PredFormula(const char *pred_name, int pred, int pred_owner = 0) : Formula(0), pred_name(pred_name), pred(pred), pred_owner(pred_owner) {}
    ~PredFormula() {
        if (pred_owner) delete [] pred_name;
    }
    bool eval(const Event *e) const override {
        return e->evalPred(pred_name, pred);
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalPred(this);
    }
    bool equalPred(const PredFormula *f) const override {
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
        return (f->equal(sub->f) && g->equal(sub->g)) || (f->equal(sub->g) && g->equal(sub->f));
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
        return (f->equal(sub->f) && g->equal(sub->g)) || (f->equal(sub->g) && g->equal(sub->f));
    }
};

struct ImpFormula : Formula {
    Formula *f, *g;

    ImpFormula(Formula *f, Formula *g) : Formula(f->is_temporal || g->is_temporal), f(f), g(g) {}
    ~ImpFormula() override {
        if (f != NULL) delete f;
        if (g != NULL) delete g;
    }
    bool eval(const Event *e) const override {
        return !f->eval(e) || g->eval(e);
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalImp(this);
    }
    bool equalImp(const ImpFormula *sub) const override {
        return f->equal(sub->f) && g->equal(sub->g);
    }
};

struct EqFormula : Formula {
    Formula *f, *g;

    EqFormula(Formula *f, Formula *g) : Formula(f->is_temporal || g->is_temporal), f(f), g(g) {}
    ~EqFormula() override {
        if (f != NULL) delete f;
        if (g != NULL) delete g;
    }
    bool eval(const Event *e) const override {
        return f->eval(e) == g->eval(e);
    }
    void accept(FormulaVisitor &v) override {
        v.visit(this);
    }

    bool equal(const Formula *f) const override {
        return f->equalEq(this);
    }
    bool equalEq(const EqFormula *sub) const override {
        return (f->equal(sub->f) && g->equal(sub->g)) || (f->equal(sub->g) && g->equal(sub->f));
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

#endif /* __FORMULA_H__ */
