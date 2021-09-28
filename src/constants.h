#ifndef __CONSTANTS_H__
#define __CONSTANTS_H__

#include "util.h"

extern int pure_mdl;
extern int grep;

struct interval {
    timestamp from, to;
};

extern interval inf_in;

#endif /* __CONSTANTS_H__ */
