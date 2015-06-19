int delete_substr(char *str, int strlen, char *substr, int sublen, char *dest) {
 int start = find_substr(str, strlen, substr, sublen), j, k;
 if (start == -1) {
  for (k = 0; k < strlen; k++) dest[k] = str[k];
  return 0;
 }
 for (j = 0; j < start; j++) dest[j] = str[j];
 for (j = start; j < strlen-sublen; j++) dest[j] = str[j+sublen];
 return 1;
}
