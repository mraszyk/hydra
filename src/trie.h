#ifndef __TRIE_H__
#define __TRIE_H__

#include <cstdlib>

template<typename T>
struct TrieNode {
    T value;
    TrieNode *next[256];

    TrieNode(T init) {
        value = init;
        for (int i = 0; i < 256; i++) next[i] = NULL;
    }
    ~TrieNode() {
        for (int i = 0; i < 256; i++) {
            if (next[i] != NULL) {
                delete next[i];
            }
        }
    }
};

struct Trie {
    TrieNode<int> root;
    int cnt = 0;

    Trie() : root(-1) {}

    int getOrAdd(const char *s);
};

extern Trie trie;

#endif /* __TRIE_H__ */
