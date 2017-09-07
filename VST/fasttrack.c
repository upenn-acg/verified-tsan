//#include <stdlib.h>
#include "threads.h"

extern void exit(int code);

#define MAX_THREADS 10
#define MAX_LOCKS 10
#define MAX_VARS 10

//Eventually, make this resizable.
typedef int vector_clock[MAX_THREADS];
typedef int tid;
typedef int var;
typedef int lock;
typedef struct epoch{int time; tid thread;} epoch;
typedef enum eorvc_tag { EPOCH, VC } eorvc_tag;
typedef union choice {epoch e; vector_clock vc;} choice;
typedef struct eorvc{eorvc_tag tag; choice data;} eorvc; 

vector_clock C[MAX_THREADS];
vector_clock L[MAX_LOCKS];
eorvc *R[MAX_VARS];
epoch *W[MAX_VARS];
lock_t *X[MAX_VARS];

int max(int a, int b){
  return (a >= b)?a:b;
}

int check_le(vector_clock v1, vector_clock v2){
  for(int i = 0; i < MAX_THREADS; i++){
    int a = v1[i];
    int b = v2[i];
    if(b < a) return 0;
  }
  return 1;
}

int check_le_e(epoch *e1, vector_clock v2){
  int t1 = e1->time;
  tid i1 = e1->thread;
  int t2 = v2[i1];
  return (t1 <= t2);
}

void instr_read(tid t, var x){
  lock_t *lx = X[x];
  acquire(lx);
  eorvc *r = R[x];
  epoch *w = W[x];
  eorvc_tag ty = r->tag;
  int ct = C[t][t];
  if(ty == EPOCH){
    epoch *re = &(r->data.e);
    int c = re->time;
    tid u = re->thread;
    if(c == ct && u == t){
      release(lx);
      return;
    }
    if(!check_le_e(w, C[t])) exit(1); //race detected
    if(check_le_e(re, C[t])){
      re->time = ct;
      re->thread = t;
      release(lx);
      return;
    }
    r->tag = VC;
    for(int i = 0; i < MAX_THREADS; i++){
      if(i == t) r->data.vc[i] = ct;
      else if(i == u) r->data.vc[i] = c;
      else r->data.vc[i] = 0;	    
    }
    release(lx);
    return;
  }
  else{
    if(check_le_e(w, C[t])){
      r->data.vc[t] = ct;
      release(lx);
      return;
    }
    exit(1); //race detected
  }
}

void instr_write(tid t, var x){
  lock_t *lx = X[x];
  acquire(lx);
  eorvc *r = R[x];
  epoch *w = W[x];
  int cx = w->time;
  int tx = w->thread;
  int ct = C[t][t];
  if(cx == ct && tx == t){
    release(lx);
    return;
  }
  if(!check_le_e(w, C[t])) exit(1); //race detected
  eorvc_tag ty = r->tag;
  if(ty == EPOCH){
    if(check_le_e(&r->data.e, C[t])){
      w->time = ct;
      w->thread = t;
      release(lx);
      return;
    }
    exit(1); //race detected
  }
  else{
    if(check_le(r->data.vc, C[t])){
      w->time = ct;
      w->thread = t;
      r->tag = EPOCH;
      r->data.e.time = 0;
      r->data.e.thread = 0;
      release(lx);
      return;
    }
    else exit(1); //race detected
  }
}

void vc_join(vector_clock tgt, vector_clock src){
  for(int i = 0; i < MAX_THREADS; i++)
    tgt[i] = max(tgt[i], src[i]);
}

void instr_acquire(tid t, lock m){
  vc_join(C[t], L[m]);
}

void instr_release(tid t, lock m){
  for(int i = 0; i < MAX_THREADS; i++)
    L[m][i] = C[t][i];
  C[t][t]++;
}

void instr_fork(tid t, tid u){
  vc_join(C[u], C[t]);
  C[t][t]++;
}

void instr_join(tid t, tid u){
  vc_join(C[t], C[u]);
  C[u][u]++;
}
