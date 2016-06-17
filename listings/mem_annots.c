extern void* malloc(unsigned long);
extern void free(void*);

void main() {
  int * t = malloc(3*sizeof(int));
  t[0] = 1;
  t[1] = 1;
  int * p = t+1;
  //@ assert \base_addr(p) == (char*)t;
  //@ assert \block_length(p) == 3 * sizeof(int);
  //@ assert \offset(p) == 1*sizeof(int);
  //@ assert \valid(p+0) && \valid(p+1);
  //@ assert \initialized(p) && !\initialized(p+1);
  free(t);
}
