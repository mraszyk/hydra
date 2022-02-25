#include "visitors.h"

#include <cstdio>
#include <cstring>

template<typename MH>
std::pair<DFA *, MH *> createMH(Regex *r, InputReader *input_reader) {
    std::vector<Formula *> fmla;
    CollectVisitor c(fmla);
    r->accept(c);
    FragVisitor f(fmla);
    r->accept(f);
    StateCount s;
    r->accept(s);
    NFA *nfa = new NFA(f.get());
    DFA *dfa = new DFA(nfa);
    int buf_len = 0;
    while ((1 << buf_len) < s.get() + 1) buf_len++;
    MonitorVisitor mv(input_reader);
    std::vector<Monitor *> sub_mon;
    Event *handle = input_reader->open_handle();
    for (size_t i = 0; i < fmla.size(); i++) {
        if (fmla[i]->is_temporal) {
            fmla[i]->accept(mv);
            sub_mon.push_back(mv.get_mon());
        } else {
            sub_mon.push_back(new EvalMonitor(fmla[i], input_reader, handle));
        }
    }

    LastReader *l_reader = new LastReader(fmla, input_reader, handle, sub_mon, buf_len);
    return make_pair(dfa, new MH(dfa, input_reader, l_reader));
}

template std::pair<DFA *, MH_FW *> createMH(Regex *r, InputReader *input_reader);
template std::pair<DFA *, MH_BW *> createMH(Regex *r, InputReader *input_reader);

void AtomRegexVisitor::visit(LookaheadRegex *r) {
    AtomFormulaVisitor v(atoms);
    r->f->accept(v);
}
void AtomRegexVisitor::visit(SymbolRegex *r) {
    AtomFormulaVisitor v(atoms);
    r->f->accept(v);
}

void PrintRegexVisitor::visit(LookaheadRegex *r) {
    fprintf(out, "(");
    PrintHydraFormulaVisitor f(out);
    r->f->accept(f);
    fprintf(out, "?)");
}
void PrintRegexVisitor::visit(SymbolRegex *r) {
    PrintHydraFormulaVisitor f(out);
    r->f->accept(f);
}

void print_fmla_hydra(const char *fname, Formula *fmla)
{
    FILE *out = open_file_type(fname, ".mdl", "w");
    PrintHydraFormulaVisitor f(out);
    fmla->accept(f);
    fclose(out);
}

static bool mystrcmp(const char *s1, const char *s2) {
    return strcmp(s1, s2) < 0;
}

void print_fmla_reelay(const char *fname, Formula *fmla)
{
    FILE *out = open_file_type(fname, ".yaml", "w");
    fprintf(out, "---\n");
    fprintf(out, "name : \"prop\"\n");
    fprintf(out, "lang : \"temporal\"\n");
    fprintf(out, "pattern : \"");
    PrintReelayFormulaVisitor f(out);
    fmla->accept(f);
    fprintf(out, "\"\n");
    fprintf(out, "with_headers : true\n");
    std::vector<const char *> atoms;
    AtomFormulaVisitor a(atoms);
    fmla->accept(a);
    sort(atoms.begin(), atoms.end(), mystrcmp);
    fprintf(out, "atoms : \"");
    for (size_t i = 0; i < atoms.size(); i++) {
        fprintf(out, "%s%s", (i == 0 ? "" : " "), atoms[i]);
    }
    fprintf(out, "\"\n");
    fclose(out);
}
