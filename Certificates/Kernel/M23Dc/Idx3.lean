module

public import Certificates.Kernel.M23Dc.Lit
public import CFSG.Quasithin.EmptyFaithful.S151S9TM23Inputs
public import CFSG.Certificates.Kernel.SporLatDcPair
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.S151S9T

theorem m23K_check : m23Wit.Ok 23 (codeSetAct 23) m23Delta m23LatK m23SLP[159]! := by
  unfold Idx3Wit.Ok Idx3Wit.dcT Idx3Wit.xT Idx3Wit.rT Idx3Wit.riT
  simp only [idTab_eq, wordTabA_eq_L, codeSetAct_eq, delta_eq, ne_eq, ← Array.toList_inj]
  exact of_decide_eq_true (by quickRfl)

end CFSG.KD.M23Dc

end
