int is_present_precond(int* t, int n, int v) {
 §$Beg_{\texttt{is\_present\_precond}}:$§
  §$\underline{\Zinit \mbox{var\_0 = 0}}$§; §$\underline{\Zinit \mbox{var\_1 = n}}$§; int var_2 = §$\underline{ \mbox{var\_0}\Zclear\ \mbox{<= var\_1}\Zclear}$§; if (!var_2) return 0;
  if (!(fvalidr(t,0,(n-1)))) return 0;
  §$\underline{\Zinit \mbox{var\_3 = n}}$§; §$\underline{\Zinit \mbox{var\_4 = 6}}$§; int var_5 = §$\underline{ \mbox{var\_3}\Zclear\ \mbox{<= var\_4}\Zclear}$§; if (!var_5) return 0;
  return 1; }

int is_present(int* t, int n, int v) {
 §$Beg_{\texttt{is\_present}}:$§
  int *old_t = t, *old_val_t = malloc(((n-1)+1)*sizeof(int)), old_n = n, old_v = v, res = 0, i = 0, iter_t;
  for(iter_t = 0; iter_t < n; iter_t++) *(old_val_t+iter_t) = *(t+iter_t); fassume(is_present_precond(t, n, v));
 §$l_0:$§
  §$\underline{\Zinit \mbox{var\_0 = 0}}$§; §$\underline{\Zinit \mbox{var\_1 = i}}$§; int var_2 = §$\underline{ \mbox{var\_0}\Zclear\ \mbox{<= var\_1}\Zclear}$§; int var_3 = var_2;
  if(var_3) { §$\underline{\Zinit \mbox{var\_4 = i}}$§; §$\underline{\Zinit \mbox{var\_5 = n}}$§; int var_6 = §$\underline{ \mbox{var\_4}\Zclear\ \mbox{<= var\_5}\Zclear}$§; var_3 = var_6; } fassert(var_3);
  while(i < n) {
   §$BegIter_{l_0}:$§
    §$\underline{\Zinit \mbox{var\_7 = n}}$§; §$\underline{\Zinit \mbox{var\_8 = i}}$§; §$\underline{\Zinit \mbox{var\_9 = var\_7}\Zclear\ \mbox{- var\_8}\Zclear}$§; int var_10 = §$\underline{ \mbox{0 <= var\_9}}$§; fassert(var_10);
    §$\underline{\Zinit \mbox{old\_variant = var\_{9}}\Zclear}$§;
    if(*(t+i) == v) { res = 1; break; } i++;
   §$EndIter_{l_0}:$§
    §$\underline{\Zinit \mbox{var\_{14} = 0}}$§; §$\underline{\Zinit \mbox{var\_{15} = i}}$§; int var_16 = §$\underline{ \mbox{var\_{14}}\Zclear\ \mbox{<= var\_{15}}\Zclear}$§; int var_17 = var_16;
    if(var_17) { §$\underline{\Zinit \mbox{var\_{18} = i}}$§; §$\underline{\Zinit \mbox{var\_{19} = n}}$§; int var_20 = §$\underline{ \mbox{var\_{18}}\Zclear\ \mbox{<= var\_{19}}\Zclear}$§; var_17 = var_20; } fassert(var_17);
    §$\underline{\Zinit \mbox{var\_{26} = n}}$§; §$\underline{\Zinit \mbox{var\_{27} = i}}$§; §$\underline{\Zinit \mbox{var\_{28} = var\_{26}}\Zclear\ \mbox{- var\_{27}}\Zclear}$§; int var_29 = §$\underline{ \mbox{var\_{28}}\Zclear\ \mbox{< old\_variant}\Zclear}$§;
    fassert(var_29);
  }
 §$End_{\texttt{is\_present}}:$§
  §$\underline{\Zinit \mbox{var\_{30} = 0}}$§; §$\underline{\Zinit \mbox{var\_{31} = res}}$§; int var_32 = §$\underline{ \mbox{var\_{30}}\Zclear\ \mbox{!= var\_{31}}\Zclear}$§; §$\underline{\Zinit \mbox{var\_{33} = 0}}$§; §$\underline{\Zinit \mbox{var\_{34} = old\_n}}$§;
  int var_35 = 0;
  for(§$\underline{\Zinit \mbox{i\_0 = var\_{33}}\Zclear}$§; §$\underline{ \mbox{i\_0 < var\_{34}}\Zclear}$§ && !var_35; §$\underline{ \mbox{i\_0++}\Zclear}$§) {
    §$\underline{\Zinit \mbox{var\_{36} = i\_0}}$§; int var_37 = §$\underline{\mbox{var\_{36}}\Zclear}$§; var_35 = *(old_val_t + var_37) == old_value; }
  fassert((!var_32 || var_35) && (!var_35 || var_32));
  free(old_val_t); return res; }
