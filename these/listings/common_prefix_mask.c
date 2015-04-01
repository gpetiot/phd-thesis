typedef unsigned char byte;
// index            0    1    2    3    4    5    6    7    8
byte  masks[] = {0x00,0x80,0xC0,0xE0,0xF0,0xF8,0xFC,0xFE,0xFF};
int longer [] = {   0,  -1,   3,  -3,   6,  -5,   7,   8,  -8};
int shorter[] = {   0,   0,   1,  -2,   2,  -4,   5,  -6,  -7};
byte gtCommonPrefixMask(byte a, byte b) {
  byte nxor = ~(a ^ b);   // a bit = 1 iff this bit is equal in a and b
  int i = 4;              // search starts in the middle of the word
  while(i > 0)            // we stop when i<=0
    if (nxor >= masks[i]) // first i bits equal,
      i = longer[i];      // try a longer prefix 
    else i = shorter[i];  // otherwise, try a shorter prefix 
  return masks[-i];       // when i<=0, masks[-i] is the answer
}
