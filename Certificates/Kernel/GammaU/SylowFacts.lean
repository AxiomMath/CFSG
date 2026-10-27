module

public import Certificates.Kernel.GammaU.Sylow0OK
public import Certificates.Kernel.GammaU.Sylow1OK
public import Certificates.Kernel.GammaU.SigmaFacts
public import CFSG.Certificates.Kernel.GammaUSylowSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUY0

open CFSG.KC.IF4C CFSG.KC.GUY CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem gens_spec :
    tlOK ASP AB ATL 3 1 = true ∧ invOK ASP ASI 3 = true ∧ wordsOK ASP ASI 3 AWD 2 = true := by
  have h := cs16973a_gens
  unfold gens at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lvl_spec {i : Nat} (hi : i < 2) :
    cntOK AO ATL AR i = true ∧ treeOK ASP AT AO ATL ATR i = true ∧ posOK AT AO APS AB i = true := by
  have h : lvl i = true := by
    have h2 := cs16973a_lvl
    simp only [Bool.and_eq_true] at h2
    interval_cases i
    exacts [h2.1, h2.2]
  unfold lvl at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem chainHypA0 : ChainHyp ASP ASI AT AO APS AB ATL AWD ATR AR 2 2 3 where
  lenO := by decide +kernel
  lenT := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h2 := by
    obtain rfl : i = 1 := by omega
    exact gens_spec.1
  inv := gens_spec.2.1
  words := gens_spec.2.2
  tree i hi := (lvl_spec hi).2.1
  pos i hi := (lvl_spec hi).2.2
  cnt i hi := (lvl_spec hi).1
  blk i hi c hc := by
    change blk i c = true
    interval_cases i
    · have : (AR.getD 0 []).length = 18 := by decide +kernel
      obtain rfl : c = 0 := by omega
      exact cs16973a_b0
    · have : (AR.getD 1 []).length = 3 := by decide +kernel
      obtain rfl : c = 0 := by omega
      exact cs16973a_b1

theorem sylowFacts0 : SylowFacts 0 :=
  sylowFacts_of CFSG.KD.GUS0.chainHyp0 (by decide +kernel) CFSG.KD.GUS0.sigmaLvl0.2 chainHypA0
    (by decide +kernel) cs16973a_sift cs16973a_conj cs16973a_ord cs16973a_nc cs16973a_cent

end CFSG.KD.GUY0

namespace CFSG.KD.GUY1

open CFSG.KC.IF4C CFSG.KC.GUY CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem gens_spec :
    tlOK ASP AB ATL 3 1 = true ∧ invOK ASP ASI 3 = true ∧ wordsOK ASP ASI 3 AWD 2 = true := by
  have h := cs16973b_gens
  unfold gens at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lvl_spec {i : Nat} (hi : i < 2) :
    cntOK AO ATL AR i = true ∧ treeOK ASP AT AO ATL ATR i = true ∧ posOK AT AO APS AB i = true := by
  have h : lvl i = true := by
    have h2 := cs16973b_lvl
    simp only [Bool.and_eq_true] at h2
    interval_cases i
    exacts [h2.1, h2.2]
  unfold lvl at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem chainHypA1 : ChainHyp ASP ASI AT AO APS AB ATL AWD ATR AR 2 2 3 where
  lenO := by decide +kernel
  lenT := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h2 := by
    obtain rfl : i = 1 := by omega
    exact gens_spec.1
  inv := gens_spec.2.1
  words := gens_spec.2.2
  tree i hi := (lvl_spec hi).2.1
  pos i hi := (lvl_spec hi).2.2
  cnt i hi := (lvl_spec hi).1
  blk i hi c hc := by
    change blk i c = true
    interval_cases i
    · have : (AR.getD 0 []).length = 18 := by decide +kernel
      obtain rfl : c = 0 := by omega
      exact cs16973b_b0
    · have : (AR.getD 1 []).length = 3 := by decide +kernel
      obtain rfl : c = 0 := by omega
      exact cs16973b_b1

theorem sylowFacts1 : SylowFacts 1 :=
  sylowFacts_of CFSG.KD.GUS1.chainHyp1 (by decide +kernel) CFSG.KD.GUS1.sigmaLvl1.2 chainHypA1
    (by decide +kernel) cs16973b_sift cs16973b_conj cs16973b_ord cs16973b_nc cs16973b_cent

end CFSG.KD.GUY1

namespace CFSG.KD.GUY

open CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem sylowFacts : ∀ i, i = 0 ∨ i = 1 → SylowFacts i := by
  rintro i (rfl | rfl)
  · exact CFSG.KD.GUY0.sylowFacts0
  · exact CFSG.KD.GUY1.sylowFacts1

end CFSG.KD.GUY

end
