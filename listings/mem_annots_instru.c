void main(void) {
  int *t;
  int *p;
  __store_block((void *)(& p),4U);
  __store_block((void *)(& t),4U);
  __full_init((void *)(& t));
  t = (int *)__e_acsl_malloc((unsigned long)((unsigned int)3 * sizeof(int)));
  __initialize((void *)(t + 0),sizeof(int));
  *(t + 0) = 1;
  __initialize((void *)(t + 1),sizeof(int));
  *(t + 1) = 1;
  __full_init((void *)(& p));
  p = t + 1;
  /*@ assert \base_addr(p) == (char *)t; */
  void *__e_acsl_base_addr;
  __e_acsl_base_addr = __base_addr((void *)p);
  e_acsl_assert(__e_acsl_base_addr == (char *)t);
  /*@ assert \block_length(p) == 3*sizeof(int); */
  unsigned long __e_acsl_block_length;
  __e_acsl_block_length = (unsigned long)__block_length((void *)p);
  e_acsl_assert((unsigned long long)__e_acsl_block_length ==
		(unsigned long long)(3 * 4));
  /*@ assert \offset(p) == 1*sizeof(int); */
  int __e_acsl_offset;
  __e_acsl_offset = __offset((void *)p);
  e_acsl_assert((unsigned int)__e_acsl_offset == (unsigned int)(1 * 4));
  /*@ assert \valid(p+0) && \valid(p+1); */
  int __e_acsl_valid;
  int __e_acsl_and;
  __e_acsl_valid = __valid((void *)(p + 0),sizeof(int));
  if (__e_acsl_valid) {
    int __e_acsl_valid_2;
    __e_acsl_valid_2 = __valid((void *)(p + 1),sizeof(int));
    __e_acsl_and = __e_acsl_valid_2;
  }
  else __e_acsl_and = 0;
  e_acsl_assert(__e_acsl_and);
  /*@ assert \initialized(p) && !\initialized(p+1); */
  int __e_acsl_initialized;
  int __e_acsl_and_2;
  __e_acsl_initialized = __initialized((void *)p,sizeof(int));
  if (__e_acsl_initialized) {
    int __e_acsl_initialized_2;
    __e_acsl_initialized_2 = __initialized((void *)(p + 1),sizeof(int));
    __e_acsl_and_2 = ! __e_acsl_initialized_2;
  }
  else __e_acsl_and_2 = 0;
  e_acsl_assert(__e_acsl_and_2);
  __e_acsl_free((void *)t);
  __delete_block((void *)(& p));
  __delete_block((void *)(& t));
  __e_acsl_memory_clean();
  return;
}
