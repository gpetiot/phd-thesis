if( x > 0 ) { 
  /*@ assert x+1 > 0; */ // never fails in unbounded arithmetics
  fassert(x+1 > 0);      // may fail in modular arithmetics  
}
