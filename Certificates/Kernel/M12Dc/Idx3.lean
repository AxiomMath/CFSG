module

public import Certificates.Kernel.M12Dc.Lit
public import CFSG.Quasithin.EmptyFaithful.S151S9TM12Inputs
public import CFSG.Certificates.Kernel.SporLatDcPair
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M12Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.S151S9T

theorem m12K_check : m12Wit.Ok 12 (codeSetAct 12) m12Delta m12LatK m12SLP[153]! := by
  unfold Idx3Wit.Ok Idx3Wit.dcT Idx3Wit.xT Idx3Wit.rT Idx3Wit.riT
  simp only [idTab_eq, wordTabA_eq_L, codeSetAct_eq, delta_eq, ne_eq, ← Array.toList_inj]
  exact of_decide_eq_true (by quickRfl)

end CFSG.KD.M12Dc

end
