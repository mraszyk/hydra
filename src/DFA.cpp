#include "DFA.h"

#include "common.h"
#include <cstdlib>
#include <cstring>

/* Patch the list of states at f.out to point to start. */
void patch(const Frag &f, NState *s)
{
    for (size_t i = 0; i < f.out.size(); i++) *f.out[i] = s;
}

NFA::NFA(const Frag &f, int state_cnt) : start(f.start), matchstate(Match, NULL, NULL), state_cnt(state_cnt + 1), list_id(0) {
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

void NFA::run_state(NState *s, const Event *e, std::vector<NState *> &l)
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
            if (e->eval(s->c)) run_state(s->out, e, l);
            break;
    }
}

DState *DFA::run(DState *s, const Event *e)
{
    std::map<Event, DState *>::iterator it = run_cache[s->idx].find(*e);
    if (it == run_cache[s->idx].end()) {
        std::vector<NState *> l;
        nfa->list_id++;

        for (size_t i = 0; i < s->l.size(); i++) nfa->run_state(s->l[i], e, l);

        sort(l.begin(), l.end());
        DState *r = lookup(l);
        return run_cache[s->idx][*e] = r;
    } else {
        return it->second;
    }
}

DState *DFA::step(DState *s) {
    if (s->step == NULL) {
        std::vector<NState *> l;
        nfa->list_id++;

        for (size_t i = 0; i < s->l.size(); i++) {
            NState *cur = s->l[i];
            if (cur->c == Wild) {
                NState *nex = cur->out;
                if (nex->lastlist != nfa->list_id) {
                    nex->lastlist = nfa->list_id;
                    l.push_back(nex);
                }
            }
        }

        sort(l.begin(), l.end());
        DState *r = lookup(l);
        return s->step = r;
    } else {
        return s->step;
    }
}
