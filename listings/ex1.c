int x;
/*@ ensures x >= \old(x)+1; assigns x; */
void g1() { x=x+2; }
/*@ ensures x >= \old(x)+1; assigns x; */
void g2() { x=x+2; }
/*@ ensures x >= \old(x)+1; assigns x; */
void g3() { x=x+2; }
/*@ ensures x >= \old(x)+4; assigns x; */
void f() { g1(); g2(); g3(); }
