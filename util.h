#ifndef UTIL_H
#define UTIL_H

struct TryLock {
    int volatile state;
    TryLock() {
        state = 0;
    }
    bool tryAcquire() {
        if (state) return false;
        return __sync_bool_compare_and_swap(&state, 0, 1);
    }
    void release() {
        state = 0;
    }
    bool isHeld() {
        return state;
    }
};
#endif /* UTIL_H */