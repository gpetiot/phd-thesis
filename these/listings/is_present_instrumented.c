int is_present(int* t, int n, int v) {
 §$Beg_{\texttt{is\_present}}:$§
  int *old_t = t; int *old_val_t = malloc(((n-1)+1)*sizeof(int)); int old_n = n;
  int old_v = v; int res§$_{\texttt{is\_present}}$§; int i; int iter_t; res§$_{\texttt{is\_present}}$§ = 0; i = 0;
  for(iter_t = 0; iter_t < n; iter_t++) old_val_t[iter_t] = t[iter_t];
  §$\underline{\Zinit \mbox{var\_{38} = 0}}$§; §$\underline{\Zinit \mbox{var\_{39} = n}}$§; int var_40 = §$\underline{ \mbox{var\_38}\Zclear\ \mbox{<= var\_{39}}\Zclear}$§; fassume(var_40);
  fassume(fvalidr(t,0,(n-1)));
  §$\underline{\Zinit \mbox{var\_{41} = n}}$§; §$\underline{\Zinit \mbox{var\_{42} = 6}}$§; int var_43 = §$\underline{ \mbox{var\_{}41}\Zclear\ \mbox{<= var\_{42}}\Zclear}$§; fassume(var_43);
 §$l_0:$§
  §$\underline{\Zinit \mbox{var\_0 = 0}}$§; §$\underline{\Zinit \mbox{var\_1 = i}}$§; int var_2 = §$\underline{ \mbox{var\_0}\Zclear\ \mbox{<= var\_1}\Zclear}$§; int var_3 = var_2;
  if(var_3) { §$\underline{\Zinit \mbox{var\_4 = i}}$§; §$\underline{\Zinit \mbox{var\_5 = n}}$§; int var_6 = §$\underline{ \mbox{var\_4}\Zclear\ \mbox{<= var\_5}\Zclear}$§; var_3 = var_6; }
  fassert(var_3);
  while(i < n && t[i] != v) {
   §$BegIter_{l_0}:$§
    §$\underline{\Zinit \mbox{var\_7 = n}}$§; §$\underline{\Zinit \mbox{var\_8 = i}}$§; §$\underline{\Zinit \mbox{var\_9 = var\_7}\Zclear\ \mbox{- var\_8}\Zclear}$§;
    int var_10 = §$\underline{ \mbox{0 <= var\_9}}$§; fassert(var_10);
    i = i+1;
   §$EndIter_{l_0}:$§
    §$\underline{\Zinit \mbox{var\_{14} = 0}}$§; §$\underline{\Zinit \mbox{var\_{15} = i}}$§; int var_16 = §$\underline{ \mbox{var\_{14}}\Zclear\ \mbox{<= var\_{15}}\Zclear}$§; int var_17 = var_16;
    if(var_17) {
      §$\underline{\Zinit \mbox{var\_{18} = i}}$§; §$\underline{\Zinit \mbox{var\_{19} = n}}$§; int var_20 = §$\underline{ \mbox{var\_{18}}\Zclear\ \mbox{<= var\_{19}}\Zclear}$§; var_17 = var_20;
    }
    fassert(var_17);
    §$\underline{\Zinit \mbox{var\_{26} = n}}$§; §$\underline{\Zinit \mbox{var\_{27} = i}}$§; §$\underline{\Zinit \mbox{var\_{28} = var\_{26}}\Zclear\ \mbox{- var\_{27}}\Zclear}$§;
    int var_29 = §$\underline{ \mbox{var\_{28}}\Zclear\ \mbox{< var\_9}\Zclear}$§; fassert(var_29);
  }
  if(i < n) { res§$_{\texttt{is\_present}}$§ = 1; }
 §$End_{\texttt{is\_present}}:$§
  §$\underline{\Zinit \mbox{var\_{30} = 0}}$§; §$\underline{\Zinit \mbox{var\_{31} = res$_{\texttt{is\_present}}$}}$§; int var_32 = §$\underline{ \mbox{var\_{30}}\Zclear\ \mbox{!= var\_{31}}\Zclear}$§;
  §$\underline{\Zinit \mbox{var\_{33} = 0}}$§; §$\underline{\Zinit \mbox{var\_{34} = old\_n}}$§;
  int var_35 = 0;
  for(§$\underline{\Zinit \mbox{i\_0 = var\_{33}}\Zclear}$§; §$\underline{ \mbox{i\_0 < var\_{34}}\Zclear}$§ && !var_35; §$\underline{ \mbox{i\_0++}\Zclear}$§) {
    §$\underline{\Zinit \mbox{var\_{36} = i\_0}}$§; int var_37 = §$\underline{\mbox{var\_{36}}\Zclear}$§; var_35 = old_val_t[var_37] == old_v; }
  fassert((!var_32 || var_35) && (!var_35 || var_32));
  free(old_val_t); return res§$_{\texttt{is\_present}}$§; }
