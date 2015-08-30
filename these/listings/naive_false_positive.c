if( x > 0 ) { 
  /*@ assert x+1 > 0; */ // never fails in unbounded arithmetics
  // naive instrumentation may fail in modular arithmetics
  fassert(x+1 > 0);      
}
