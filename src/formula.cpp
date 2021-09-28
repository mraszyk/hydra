#include "formula.h"

TestRegex::~TestRegex() {
    if (f_owner) delete f;
}
bool TestRegex::equalTest(const TestRegex *r) const {
    return f->equal(r->f);
}

AtomicConsumeRegex::~AtomicConsumeRegex() {
    if (f_owner) delete f;
}
bool AtomicConsumeRegex::equalAtomic(const AtomicConsumeRegex *r) const {
    return f->equal(r->f);
}
