/*@ predicate is_rgf(int *a, integer n) =
      a[0] == 0 &&
        \forall integer i; 1 <= i < n ==>
          (0 <= a[i] <= a[i-1]+1); */

/*@ lemma max_rgf:
  \forall int* a; \forall integer n;
    is_rgf(a, n) ==>
      (\forall integer i; 0 <= i < n ==>
        a[i] <= i); */

/*@ requires n > 0;
    requires \valid(a+(0..n-1));
    requires 1 <= i <= n-1;
    requires is_rgf(a,i+1);
    assigns a[i+1..n-1];
    ensures is_rgf(a,n); */
void g(int a[], int n, int i) {
 int k;
 /*@ loop invariant i+1 <= k <= n;
     loop invariant is_rgf(a,k);
     loop assigns k, a[i+1..n-1];
     loop variant n-k; */
 for (k = i+1; k < n; k++) a[k] = 0;
}

/*@ requires n > 0;
    requires \valid(a+(0..n-1));
    requires is_rgf(a,n);
    assigns a[1..n-1];
    ensures is_rgf(a,n);
    ensures \result == 1 ==>
     \exists integer j; 0 <= j < n &&
      (\at(a[j],Pre) < a[j] &&
       \forall integer k; 0 <= k < j ==>
         \at(a[k],Pre) == a[k]); */
int f(int a[], int n) {
 int i,k;
 /*@ loop invariant 0 <= i <= n-1;
     loop assigns i;
     loop variant i; */
 for (i = n-1; i >= 1; i--)
  if (a[i] <= a[i-1]) { break; }
 if (i == 0) { return 0; } // Last RGF.
 //@ assert a[i]+1 <= 2147483647;
 a[i] = a[i] + 1;
 g(a,n,i);
 /*@ assert \forall integer l;
       0 <= l < i ==>
         \at(a[l],Pre) == a[l]; */
 return 1;
}
