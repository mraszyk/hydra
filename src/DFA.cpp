#include "DFA.h"

#include "common.h"
#include <cstdlib>
#include <cstring>

/* Patch the list of states at f.out to point to start. */
void patch(const Frag &f, NState *s)
{
    for (size_t i = 0; i < f.out.size(); i++) *f.out[i] = s;
}

NFA::NFA(const Frag &f) : start(f.start), matchstate(Match, NULL, NULL), list_id(0) {
    patch(f, &matchstate);
}

NFA::~NFA() {
    list_id++;
    std::vector<NState *> l;
    collectStates(start, l);
    for (size_t i = 0; i < l.size(); i++) delete l[i];
}

void NFA::collectStates(NState *s, std::vector<NState *> &l)
{
    if (s == NULL || s == &matchstate || s->lastlist == list_id) return;
    s->lastlist = list_id;
    l.push_back(s);
    collectStates(s->out, l);
    collectStates(s->out1, l);
}

void NFA::run_state(NState *s, const vector<int> &e, std::vector<NState *> &l)
{
    CHECK(s != NULL);
    if (s->lastlist == list_id) return;
    s->lastlist = list_id;
    l.push_back(s);
    switch (s->c) {
        case Match:
        case Wild:
            break;
        case Split:
            run_state(s->out, e, l);
            run_state(s->out1, e, l);
            break;
        default:
            if (s->c < e.size() && e[s->c]) run_state(s->out, e, l);
            break;
    }
}

void NFA::run_states(const std::vector<NState *> &s, const vector<int> &e, std::vector<NState *> &l)
{
  list_id++;
  for (size_t i = 0; i < s.size(); i++) run_state(s[i], e, l);
  sort(l.begin(), l.end());
}

DFA::~DFA() {
    delete nfa;
    for (std::map<std::vector<NState *>, DState *>::iterator it = state_cache.begin(); it != state_cache.end(); it++) {
        delete it->second;
    }
}

DState *DFA::lookup(const std::vector<NState *> &l) {
    std::map<std::vector<NState *>, DState *>::iterator it = state_cache.find(l);
    if (it == state_cache.end()) {
        DState *s = new DState(nfa, l, dstate_cnt++);
        state_cache[l] = s;
        run_cache.resize(dstate_cnt);
        return s;
    } else {
        return it->second;
    }
}

DState *DFA::run(DState *s, const vector<int> &e)
{
    std::map<vector<int>, DState *>::iterator it = run_cache[s->idx].find(e);
    if (it == run_cache[s->idx].end()) {
        std::vector<NState *> l;
        nfa->run_states(s->l, e, l);

        std::vector<NState *> step;
        nfa->list_id++;
        for (size_t i = 0; i < l.size(); i++) {
            NState *cur = l[i];
            if (cur->c == Wild) {
                NState *nex = cur->out;
                if (nex->lastlist != nfa->list_id) {
                    nex->lastlist = nfa->list_id;
                    step.push_back(nex);
                }
            }
        }
        sort(step.begin(), step.end());

        DState *r = lookup(step);
        return run_cache[s->idx][e] = r;
    } else {
        return it->second;
    }
}
