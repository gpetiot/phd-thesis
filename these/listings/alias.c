int x = 1;
int *p = &x;

/*@ assigns x; */
void f() {
  *p = 2;
}
