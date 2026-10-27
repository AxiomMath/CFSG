module

public import Certificates.Kernel.Sporadic.Fi24Base.Check
public import Certificates.Kernel.Sporadic.Fi24Net.Letters
public import CFSG.Certificates.Kernel.Spor.Fi24BaseSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixPMain
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound

public section

namespace CFSG.KD.Fi24Base

open CFSG.KC.Fi24Base CFSG.KC.Fi24NetPt CFSG.KC.Fi24FixP CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt
  CFSG.KD.Fi24Net CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi24.Native Timmesfeld.Fi24Cl
  CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.Fi24Cfg
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Solomon.Coordinator.Fi24PairSize

theorem nv_LN {l : Nat} (hl : l < 26) : NV (NW (l / 2)) :=
  (net_spec (nck_spec _ (by omega))).1

theorem LN_lt {l x : Nat} (hl : l < 26) (hx : x < 306936) : LN NW l x < 306936 := by
  unfold LN
  split_ifs
  · exact (nets (by omega) hx).1
  · exact (nets (by omega) hx).2.1

theorem LN_lt19 {l q : Nat} (hl : l < 26) (hq : q < 524288) : LN NW l q < 524288 := by
  unfold LN
  split_ifs
  · exact pF_lt (nv_LN hl) hq
  · exact pR_lt (nv_LN hl) hq

section

variable {O : Enum}
  (hA : ∀ x < 306936, ap O.alpha x = CFSG.KC.Fi24Orb.oA (CFSG.KD.Fi24Orb.OL x))
  (hB : O.beta.size = 306936 ∧
    ∀ x < 306936, ap O.beta x = CFSG.KC.Fi24Orb.oB (CFSG.KD.Fi24Orb.OL x))
include hA hB

theorem cfgCheck_true : cfgCheck O = true := by
  obtain ⟨hS, hL⟩ := letters O hA hB
  rw [CFSG.KS.Fi24Base.cfgCheck_eq (f := letN NW) hS
    (fun l hl x hx => by rw [hL l hl x hx, letN_eq])
    (fun l hl x hx => by rw [letN_eq]; exact LN_lt hl hx)]
  exact cfg_ok

theorem invCheck_true : invCheck O = true := by
  obtain ⟨hS, hL⟩ := letters O hA hB
  rw [CFSG.KS.Fi24Base.invCheck_eq (f := letN NW) hS
    (fun l hl x hx => by rw [hL l hl x hx, letN_eq])
    (fun l hl x hx => by rw [letN_eq]; exact LN_lt hl hx)]
  exact inv_ok

theorem fi24RepFixOK_true : fi24RepFixOK O = true :=
  CFSG.KS.Fi24FixP.fi24RepFixOK_of (σ := LN NW) (A := planeL NW) (letters O hA hB).2
    (fun _ hl _ hx => LN_lt hl hx) (fun _ hl _ hq => LN_lt19 hl hq)
    (fun _ hl v q _ => testBit_planeL (nv_LN hl) v q) fix_ok

theorem fixCnt_true : ∀ d ∈ repFixData, fixCnt (wordTab (mkCtx O) d.1) = d.2 := by
  have hw : ∀ d ∈ repFixData, ∀ l ∈ d.1, l < 26 := by decide
  have h := fix_ok
  rw [List.all_eq_true] at h
  intro d hd
  exact CFSG.KS.Fi24FixP.fixCnt_of (σ := LN NW) (A := planeL NW) (letters O hA hB).2
    (fun _ hl _ hx => LN_lt hl hx) (fun _ hl _ hq => LN_lt19 hl hq)
    (fun _ hl v q _ => testBit_planeL (nv_LN hl) v q) (hw d hd) (h d hd)

end

end CFSG.KD.Fi24Base

end
