module

public import Certificates.Data.Kernel.FzUT.BH2
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.FzBMod

theorem ch441796_h2consts (c : Bool) : h2Consts c (h2D c) = true := by cases c <;> quickRfl

theorem ch441796_h2sl (c : Bool) : h2SLOK c h2SL = true := by cases c <;> quickRfl

theorem ch441796_h2cover (c : Bool) : h2Cover c (h2D c) h2SL h2Rec = true := by
  cases c <;> quickRfl

theorem ch441796_h2rec (c : Bool) : allL h2Rec (h2RecOK c h2R1) = true := by cases c <;> quickRfl

theorem ch441796_h2srchI : allL h2R1 (h2Srch true (h2D true) h2SL) = true := by quickRfl

theorem ch441796_h2srchII : allL h2R1 (h2Srch false (h2D false) h2SL) = true := by quickRfl

end CFSG.KC.FzBMod
