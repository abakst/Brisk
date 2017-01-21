#define __K__ 5
/** Demonstration for objects */
#define __RECV__(_ty, _x) atomic { _ty _x; \
if \
:: chan_##_ty[1*0 + _pid]?_x \
fi }

#define __SEND__(_ty,_to,_msg) { chan_##_ty[1*_pid + _to]!_msg }

typedef T1 {
  bit top;
}

chan chan_T1[1] = [__K__] of { T1 }
int A;
int B;
int C;
int D_set;
int E_set;

init {
  int A = _pid;
  __SEND__(T1,A,A);
  __RECV__(T1,who);
}