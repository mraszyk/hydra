#ifndef __DFA_H__
#define __DFA_H__

#include "common.h"
#include "util.h"

#include <map>
#include <vector>

/*
 * Represents an NFA state plus zero or one or two arrows exiting.
 * If c == Match, no arrows out; matching state.
 * If c == Split, unlabeled arrows to out and out1 (must be != NULL).
 * If c == Wild, unlabeled arrow to out.
 * Otherwise, labeled arrow with c-th formula to out.
 */
enum
{
    Match = -1,
    Split = -2,
    Wild = -3
};
struct NState
{
    int c;
    NState *out;
    NState *out1;
    int lastlist;

    NState(int c, NState *out, NState *out1) : c(c), out(out), out1(out1), lastlist(0) {}
};

/*
 * A partially built NFA without the matching state filled in.
 * Frag.start points at the start state.
 * Frag.out is a list of places that need to be set to the
 * next state for this fragment.
 */
struct Frag
{
    NState *start;
    std::vector<NState **> out;
};

/* Patch the list of states at out to point to start. */
void patch(const Frag &f, NState *s);

struct NFA {
    NState *start;
    NState matchstate; /* matching state */
    int list_id;

    NFA(const Frag &f);
    ~NFA();

    /* Collect all states (except matchstate) into a list. */
    void collectStates(NState *s, std::vector<NState *> &l);

    /* Follow Split arrows and matching labeled arrows to create a closed state set. */
    void run_state(NState *s, const vector<int> &e, std::vector<NState *> &l);
    void run_states(const std::vector<NState *> &s, const vector<int> &e, std::vector<NState *> &l);
};

struct DState
{
    NFA *nfa;
    std::vector<NState *> l;
    int accept;
    size_t idx;

    DState(NFA *nfa, const std::vector<NState *> &l, size_t idx) : nfa(nfa), l(l), idx(idx) {
        std::vector<NState *> close;
        nfa->run_states(l, vector<int>(), close);
        accept = 0;
        for (size_t i = 0; !accept && i < close.size(); i++) {
            if (close[i]->c == Match) {
                accept = 1;
            }
        }
    }
};

class DFA {
    NFA *nfa;
    std::map<std::vector<NState *>, DState *> state_cache;
    std::vector<std::map<vector<int>, DState *> > run_cache;
    size_t dstate_cnt;

public:
    DState *init;
    DState *empty;

    DFA(NFA *nfa) : nfa(nfa), dstate_cnt(0) {
        init = lookup(std::vector<NState *>(1, nfa->start));
        empty = lookup(std::vector<NState *>());
    }
    ~DFA();

    size_t get_cnt() {
        return dstate_cnt;
    }
    DState *lookup(const std::vector<NState *> &l);
    DState *run(DState *s, const vector<int> &e);
};

#endif /* __DFA_H__ */
