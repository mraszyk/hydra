#include "formula.h"

LookaheadRegex::~LookaheadRegex() {
    if (f_owner) delete f;
}
bool LookaheadRegex::equalLookahead(const LookaheadRegex *r) const {
    return f->equal(r->f);
}

SymbolRegex::~SymbolRegex() {
    if (f_owner) delete f;
}
bool SymbolRegex::equalSymbol(const SymbolRegex *r) const {
    return f->equal(r->f);
}
