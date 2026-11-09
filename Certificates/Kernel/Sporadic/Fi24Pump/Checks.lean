module

public import Certificates.Kernel.Sporadic.Fi24Pump.Data
import Certificates.Kernel.Sporadic.Fi24Net.PTabSound
public import Certificates.Kernel.Sporadic.Fi24Kit.Split

set_option Elab.async false

public section

#kn_fixS CFSG.KD.Fi24Pump.Ck.X0
  (CFSG.KC.Fi24FixP.walkP (CFSG.KC.Fi24NetPt.planeL CFSG.KD.Fi24Net.NW)
    (CFSG.KC.Fi24Kn.nthW CFSG.KD.Fi24Pump.J.V (nat_lit 0))) 4

#kn_fixS CFSG.KD.Fi24Pump.Ck.X1
  (CFSG.KC.Fi24FixP.walkP (CFSG.KC.Fi24NetPt.planeL CFSG.KD.Fi24Net.NW)
    (CFSG.KC.Fi24Kn.nthW CFSG.KD.Fi24Pump.J.V (nat_lit 1))) 4

#kn_fixS CFSG.KD.Fi24Pump.Ck.X2
  (CFSG.KC.Fi24FixP.walkP (CFSG.KC.Fi24NetPt.planeL CFSG.KD.Fi24Net.NW)
    (CFSG.KC.Fi24Kn.nthW CFSG.KD.Fi24Pump.J.V (nat_lit 2))) 4

#kn_fixS CFSG.KD.Fi24Pump.Ck.X3
  (CFSG.KC.Fi24FixP.walkP (CFSG.KC.Fi24NetPt.planeL CFSG.KD.Fi24Net.NW)
    (CFSG.KC.Fi24Kn.nthW CFSG.KD.Fi24Pump.J.V (nat_lit 3))) 4

namespace CFSG.KD.Fi24Pump.Ck

theorem p0 : CFSG.KD.Fi24Pump.pck (nat_lit 0) = true := by
  unfold CFSG.KD.Fi24Pump.pck CFSG.KC.Fi24PumpK.pairOK
  rw [CFSG.KD.Fi24Kit.Split.fixOK_eq, ← CFSG.KD.Fi24Net.letPT_eq, X0.eq]
  quickRfl

theorem p1 : CFSG.KD.Fi24Pump.pck (nat_lit 1) = true := by
  unfold CFSG.KD.Fi24Pump.pck CFSG.KC.Fi24PumpK.pairOK
  rw [CFSG.KD.Fi24Kit.Split.fixOK_eq, ← CFSG.KD.Fi24Net.letPT_eq, X1.eq]
  quickRfl

theorem p2 : CFSG.KD.Fi24Pump.pck (nat_lit 2) = true := by
  unfold CFSG.KD.Fi24Pump.pck CFSG.KC.Fi24PumpK.pairOK
  rw [CFSG.KD.Fi24Kit.Split.fixOK_eq, ← CFSG.KD.Fi24Net.letPT_eq, X2.eq]
  quickRfl

theorem p3 : CFSG.KD.Fi24Pump.pck (nat_lit 3) = true := by
  unfold CFSG.KD.Fi24Pump.pck CFSG.KC.Fi24PumpK.pairOK
  rw [CFSG.KD.Fi24Kit.Split.fixOK_eq, ← CFSG.KD.Fi24Net.letPT_eq, X3.eq]
  quickRfl

end CFSG.KD.Fi24Pump.Ck

end
