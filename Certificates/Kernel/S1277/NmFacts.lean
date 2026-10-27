module

public import Certificates.Kernel.S1277.ML
public import Certificates.Kernel.S1277.GmFacts

public section

namespace CFSG.KP.S1277ML

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KD.S1277Gm CFSG.KC.S1277ML

theorem nm6_eqP : nm6 = (gm6P ++ gm6P.map sigP).map B6.ofP := by
  rw [CFSG.KP.S1277Gm.nm6_eq, CFSG.KS.S1277Gm.eq_of_eqB6 _ _ sig_ok, List.map_append]

end CFSG.KP.S1277ML

end
