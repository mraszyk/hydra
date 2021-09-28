#ifndef __UTIL_H__
#define __UTIL_H__

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#define CHECK(x) assert(x);

typedef int32_t timestamp;
typedef int32_t timestamp_delta;
const timestamp MAX_TIMESTAMP = 0x7FFFFFFF;

enum Boolean {
    FALSE, TRUE, UNRESOLVED
};

Boolean BooleanAnd(Boolean b1, Boolean b2);
Boolean BooleanOr(Boolean b1, Boolean b2);
Boolean BooleanImp(Boolean b1, Boolean b2);
Boolean BooleanEq(Boolean b1, Boolean b2);
Boolean BooleanNot(Boolean b);

struct BoolVerdict {
    timestamp ts;
    bool b;

    BoolVerdict() {}
    BoolVerdict(timestamp ts, bool b) : ts(ts), b(b) {}
    bool operator==(const BoolVerdict &bv) const {
        return ts == bv.ts && b == bv.b;
    }
};

struct BooleanVerdict {
    timestamp ts;
    Boolean b;

    BooleanVerdict(timestamp ts, Boolean b) : ts(ts), b(b) {}
    bool operator==(const BooleanVerdict &bv) const {
        return ts == bv.ts && b == bv.b;
    }
    BooleanVerdict operator!() const {
        return BooleanVerdict(this->ts, BooleanNot(this->b));
    }
    BooleanVerdict operator&&(const BooleanVerdict &w) const {
        CHECK(this->ts == w.ts);
        return BooleanVerdict(this->ts, BooleanAnd(this->b, w.b));
    }
    BooleanVerdict operator||(const BooleanVerdict &w) const {
        CHECK(this->ts == w.ts);
        return BooleanVerdict(this->ts, BooleanOr(this->b, w.b));
    }
    BooleanVerdict imp(const BooleanVerdict &w) const {
        CHECK(this->ts == w.ts);
        return BooleanVerdict(this->ts, BooleanImp(this->b, w.b));
    }
    BooleanVerdict eq(const BooleanVerdict &w) const {
        CHECK(this->ts == w.ts);
        return BooleanVerdict(this->ts, BooleanEq(this->b, w.b));
    }
};

int parseNumber(const char *s, size_t *pos, timestamp *n);

FILE *open_file_type(const char *prefix, const char *ftype, const char *mode);

#endif /* __UTIL_H__ */
