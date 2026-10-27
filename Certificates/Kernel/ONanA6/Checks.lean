module

public import Certificates.Data.Kernel.ONanA6
public import Certificates.Kernel.ONanA6.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.ONanA6

open CFSG.KC.ONanA6

theorem hAut : cAut la lc rc = true := by quickRfl

theorem hExp : cExp la = true := by quickRfl

theorem hOrd : cOrd lc gx u0 = true := by quickRfl

theorem hU : cU u0 u2 u3 = true := by quickRfl

theorem hPc : cPc lc pc u0 u2 u3 = true := by quickRfl

theorem hDist : cDist pc u0 u3 = true := by quickRfl

theorem hDs : cDs lc ds u0 = true := by quickRfl

theorem hEs : cEs pc es u0 u2 u3 = true := by quickRfl

theorem hRelA : cRelA pc ds u0 u2 u3 = true := by quickRfl

theorem hFix : cFix la pc gc ds es u0 u2 u3 = true := by quickRfl

theorem hk : c6151 lc rc gc la gx pc ds es u0 u2 u3 = true := by
  rw [c6151.eq_1, hAut, hExp, hOrd, hU, hPc, hDist, hDs, hEs, hRelA, hFix]
  rfl

end CFSG.KD.ONanA6

end
