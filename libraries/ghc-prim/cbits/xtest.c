#include "Rts.h"

/* No support for TSX */
extern StgWord hs_xtest();
StgWord
hs_xtest()
{
  return 0;
}

