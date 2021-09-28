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
    NFA *nfa = new NFA(f.get(), s.get());
    DFA *dfa = new DFA(nfa);
    int buf_len = 0;
    while ((1 << buf_len) < s.get() + 1) buf_len++;
    MonitorVisitor mv(input_reader);
    Event *ap_handle = input_reader->open_handle();
    std::vector<Monitor *> sub_mon;
    for (size_t i = 0; i < fmla.size(); i++) {
        if (fmla[i]->is_temporal) {
            fmla[i]->accept(mv);
            sub_mon.push_back(mv.get_mon());
        } else {
            sub_mon.push_back(new EvalMonitor(fmla[i], input_reader, ap_handle));
        }
    }

    LastReader *l_reader = new LastReader(input_reader, fmla, ap_handle, sub_mon, buf_len);
    return make_pair(dfa, new MH(dfa, l_reader));
}

template std::pair<DFA *, MH_FW *> createMH(Regex *r, InputReader *input_reader);
template std::pair<DFA *, MH_BW *> createMH(Regex *r, InputReader *input_reader);

template<typename MH>
std::pair<DFA *, MH *> createConsumeMH(ConsumeRegex *r, InputReader *input_reader) {
    std::vector<Formula *> fmla;
    CollectConsumeVisitor c(fmla);
    r->accept(c);
    FragConsumeVisitor f(fmla);
    r->accept(f);
    NullableConsumeVisitor nv;
    r->accept(nv);
    if (nv.nullable()) {
        f.nullate();
    }
    ConsumeStateCount s;
    r->accept(s);
    NFA *nfa = new NFA(f.get(), s.get());
    DFA *dfa = new DFA(nfa);
    int buf_len = 0;
    while ((1 << buf_len) < s.get() + 1) buf_len++;
    MonitorVisitor mv(input_reader);
    Event *ap_handle = input_reader->open_handle();
    std::vector<Monitor *> sub_mon;
    for (size_t i = 0; i < fmla.size(); i++) {
        sub_mon.push_back(new EvalMonitor(fmla[i], input_reader, ap_handle));
    }
    LastReader *l_reader = new LastReader(input_reader, fmla, ap_handle, sub_mon, buf_len);
    return make_pair(dfa, new MH(dfa, l_reader));
}

template std::pair<DFA *, MH_FW *> createConsumeMH(ConsumeRegex *r, InputReader *input_reader);
template std::pair<DFA *, MH_BW *> createConsumeMH(ConsumeRegex *r, InputReader *input_reader);

void AtomRegexVisitor::visit(TestRegex *r) {
    AtomFormulaVisitor v(atoms);
    r->f->accept(v);
}

void AtomConsumeRegexVisitor::visit(AtomicConsumeRegex *r) {
    AtomFormulaVisitor v(atoms);
    r->f->accept(v);
}

void PrintHydraRegexVisitor::visit(TestRegex *r) {
    fprintf(out, "(");
    PrintHydraFormulaVisitor f(out);
    r->f->accept(f);
    fprintf(out, "?)");
}

void PrintConsumeRegexVisitor::visit(AtomicConsumeRegex *r) {
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

void print_fmla_monpoly(const char *fname, Formula *fmla)
{
    FILE *out = open_file_type(fname, ".mfotl", "w");
    PrintMonpolyVisitor f(out);
    fmla->accept(f);
    fclose(out);
}

static bool mystrcmp(const char *s1, const char *s2) {
    return strcmp(s1, s2) < 0;
}

void print_regex_reelay(const char *fname, ConsumeRegex *r) {
    FILE *out = open_file_type(fname, ".yaml", "w");
    fprintf(out, "---\n");
    fprintf(out, "name : \"rand\"\n");
    fprintf(out, "lang : \"regex\"\n");
    fprintf(out, "pattern : \"");
    PrintConsumeRegexVisitor f(out);
    r->accept(f);
    fprintf(out, "\"\n");
    fprintf(out, "with_headers : true\n");
    std::vector<const char *> atoms;
    AtomConsumeRegexVisitor a(atoms);
    r->accept(a);
    sort(atoms.begin(), atoms.end(), mystrcmp);
    fprintf(out, "atoms : \"");
    for (size_t i = 0; i < atoms.size(); i++) {
        fprintf(out, "%s%s", (i == 0 ? "" : " "), atoms[i]);
    }
    fprintf(out, "\"\n");
    fclose(out);
}

void print_fmla_reelay(const char *fname, Formula *fmla)
{
    FILE *out = open_file_type(fname, ".yaml", "w");
    fprintf(out, "---\n");
    fprintf(out, "name : \"rand\"\n");
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

void print_fmla_rymtl(const char *fname, Formula *fmla)
{
    FILE *out = open_file_type(fname, ".rmtl", "w");
    PrintRymtlVisitor f(out);
    fmla->accept(f);
    fclose(out);
}

void print_fmla_r2u2(const char *fname, Formula *fmla)
{
    FILE *out = open_file_type(fname, ".mltl", "w");
    PrintR2U2Visitor f(out);
    fmla->accept(f);
    fclose(out);
}
