module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24DcInputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TM24Inputs
public import CFSG.Certificates.Kernel.SporLatDcPair
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M24Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.Quasithin.S151S9T

theorem delta_eqK : m24Delta = Δc := by
  rw [m24Delta, CFSG.KC.E64F.sortN_eq]
  decide

theorem m24K_check : m24Wit.Ok 24 (codeSetAct 24) m24Delta m24LatK m24SLP[162]! ∧
    (∀ j < 13, ∀ jj < 13, (GensIn (codeSetAct 24) m24Delta m24LatK j jj ↔ jj ∈ m24Incl[j]!)) := by
  constructor
  · unfold Idx3Wit.Ok Idx3Wit.dcT Idx3Wit.xT Idx3Wit.rT Idx3Wit.riT
    simp only [idTab_eq, wordTabA_eq_L, codeSetAct_eq, delta_eqK, ne_eq, ← Array.toList_inj]
    exact of_decide_eq_true (by quickRfl)
  · simp only [codeSetAct_eq, delta_eqK]
    exact of_decide_eq_true (by quickRfl)

end CFSG.KD.M24Dc

end
