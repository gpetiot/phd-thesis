/*@ requires 0 < sublen <= strlen;
  @ requires \valid(str+(0..strlen-1)) && \valid(substr+(0..sublen-1));
  @ assigns \nothing;
  @ behavior found:
  @  assumes \exists integer i; 0 <= i < strlen-sublen && 
  @   (\forall integer j; 0 <= j < sublen ==> str[i+j] == substr[j]);
  @  ensures 0 <= \result < strlen-sublen;
  @  ensures \forall integer j; 0 <= j < sublen ==> str[\result+j] == substr[j];
  @ behavior not_found:
  @  assumes \forall integer i; 0 <= i < strlen-sublen ==> 
  @   (\exists integer j; 0 <= j < sublen && str[i+j] != substr[j]);
  @  ensures \result == -1; */
int find_substr(char *str, int strlen, char *substr, int sublen);