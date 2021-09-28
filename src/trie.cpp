#include "trie.h"

#include <cstdlib>

Trie trie;

int Trie::getOrAdd(const char *s)
{
    TrieNode<int> *cur = &root;

    while (*s != 0) {
        if (cur->next[*s] == NULL) {
            cur->next[*s] = new TrieNode<int>(-1);
        }
        cur = cur->next[*s++];
    }

    if (cur->value == -1) {
        cur->value = cnt++;
    }

    return cur->value;
}
