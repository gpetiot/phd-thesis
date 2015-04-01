//@ assert x+1 <= INT_MAX; 
// fails with x = INT_MAX since INT_MAX + 1 does not overflow in ACSL

fassert(x+1 <= 2147483647); // naive instrumentation: never fails in modular arithmetics

// correct instrumentation with unbounded integers:
Z_t var_0; Z_init(var_0); Z_set(var_0, x); Z_t var_1; Z_init(var_1); Z_set(var_1, 1);
Z_t var_2; Z_init(var_2); Z_add(var_2, var_0, var_1); Z_clear(var_0); Z_clear(var_1);
Z_t var_3; Z_init(var_3); Z_set(var_3, 2147483647); int var_4 = Z_le(var_2, var_3);
Z_clear(var_2); Z_clear(var_3); fassert(var_4);

// correct instrumentation in abbreviated notation:
§$\underline{\Zinit \mbox{var\_0 = x}}$§; §$\underline{\Zinit \mbox{var\_1 = 1}}$§; §$\underline{\Zinit \mbox{var\_2 = var\_0}\Zclear\ \mbox{+ var\_1}\Zclear}$§; §$\underline{\Zinit \mbox{var\_3 = 2147483647}}$§;
int var_4 = §$\underline{\mbox{var\_2}\Zclear\ \mbox{<= var\_3}\Zclear}$§; fassert(var_4);
