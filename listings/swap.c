/*@ requires \valid(a) && \valid(b);
    requires \separated(a,b);
    assigns *a, *b;
    ensures *a == \at(*b,Pre);
    ensures *b == \at(*a,Pre); */
void swap(int* a, int* b);
