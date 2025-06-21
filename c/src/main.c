#include <stdio.h>
#include <stdint.h>

// typedef struct CTransysSolver CTransysSolver;

#ifdef __cplusplus
extern "C" {
#endif

extern void* transys_solver_new(int rseed);

#ifdef __cplusplus
}
#endif

int main() {
    void* ts = transys_solver_new(42);
    printf("Created solver at %p\n", ts);

    return 0;
}