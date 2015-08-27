/*@ requires 0 <= n
             && \valid(t+(0..n-1));
    typically n <= 6;
    ensures \result != 0 <==> \exists integer i; 0<=i<=\old(n)-1
                                && \old(t[i])==\old(v); */
int is_present(int* t, int n, int v) {
  §$Beg_{\texttt{is\_present}}:$§ int res§$_{\texttt{is\_present}}$§; int i; res§$_{\texttt{is\_present}}$§ = 0; i = 0;
 l§$_0$§: 
  /*@ loop invariant 0 <= i && i <= n;
      loop variant n - i; */
  while (i < n && t[i] != v) {
    §$BegIter_{l_0}:$§
    i = i+1;
    §$EndIter_{l_0}:$§ ;
  }
  if(i < n) { res§$_{\texttt{is\_present}}$§ = 1; }
 §$End_{\texttt{is\_present}}:$§ return res§$_{\texttt{is\_present}}$§;
}
