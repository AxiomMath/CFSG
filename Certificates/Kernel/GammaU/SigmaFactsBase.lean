
module

public import Certificates.Kernel.GammaU.Sigma0OK
public import Certificates.Kernel.GammaU.Sigma1OK
public import CFSG.Certificates.Kernel.GammaUSigmaSoundBase

set_option maxRecDepth 100000

@[expose] public section

namespace CFSG.KD.GUS0

open CFSG.KC.IF4C CFSG.KC.GUS CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem gens_spec : tlOK SP B TL 11 1 = true ∧ tlOK SP B TL 11 2 = true ∧
    tlOK SP B TL 11 3 = true ∧ tlOK SP B TL 11 4 = true ∧ invOK SP SI 11 = true ∧
    wordsOK SP SI 11 WD 2 = true := by
  have h := cs16981a_gens
  unfold gens at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem lvl_spec {i : Nat} (hi : i < 5) :
    cntOK O TL R i = true ∧ treeOK SP T O TL TR i = true ∧ posOK T O PS B i = true := by
  have h : lvl i = true := by
    interval_cases i
    exacts [cs16981alv0, cs16981alv1, cs16981alv2, cs16981alv3, cs16981alv4]
  unfold lvl at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem blk_spec {i : Nat} (hi : i < 5) (c : Nat) (hc : 32 * c < (R.getD i []).length) :
    blkOK SP T O TL R i c = true := by
  change blk i c = true
  interval_cases i
  · have : (R.getD 0 []).length = 36 := by decide +kernel
    exact cs16981a0all c (by omega : c < 2)
  · have : (R.getD 1 []).length = 150 := by decide +kernel
    exact cs16981a1all c (by omega : c < 5)
  · have : (R.getD 2 []).length = 28 := by decide +kernel
    exact cs16981a2all c (by omega : c < 1)
  · have : (R.getD 3 []).length = 40 := by decide +kernel
    exact cs16981a3all c (by omega : c < 2)
  · have : (R.getD 4 []).length = 2 := by decide +kernel
    exact cs16981a4all c (by omega : c < 1)

theorem chainHyp0 : ChainHyp SP SI T O PS B TL WD TR R 5 2 11 where
  lenO := by decide +kernel
  lenT := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h5 := by
    obtain ⟨h1', h2, h3, h4, -, -⟩ := gens_spec
    interval_cases i
    exacts [h1', h2, h3, h4]
  inv := gens_spec.2.2.2.2.1
  words := gens_spec.2.2.2.2.2
  tree i hi := (lvl_spec hi).2.1
  pos i hi := (lvl_spec hi).2.2
  cnt i hi := (lvl_spec hi).1
  blk i hi c hc := blk_spec hi c hc

end CFSG.KD.GUS0

namespace CFSG.KD.GUS1

open CFSG.KC.IF4C CFSG.KC.GUS CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem gens_spec : tlOK SP B TL 12 1 = true ∧ tlOK SP B TL 12 2 = true ∧
    tlOK SP B TL 12 3 = true ∧ tlOK SP B TL 12 4 = true ∧ invOK SP SI 12 = true ∧
    wordsOK SP SI 12 WD 2 = true := by
  have h := cs16981b_gens
  unfold gens at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem lvl_spec {i : Nat} (hi : i < 5) :
    cntOK O TL R i = true ∧ treeOK SP T O TL TR i = true ∧ posOK T O PS B i = true := by
  have h : lvl i = true := by
    interval_cases i
    exacts [cs16981blv0, cs16981blv1, cs16981blv2, cs16981blv3, cs16981blv4]
  unfold lvl at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem blk_spec {i : Nat} (hi : i < 5) (c : Nat) (hc : 32 * c < (R.getD i []).length) :
    blkOK SP T O TL R i c = true := by
  change blk i c = true
  interval_cases i
  · have : (R.getD 0 []).length = 36 := by decide +kernel
    exact cs16981b0all c (by omega : c < 2)
  · have : (R.getD 1 []).length = 150 := by decide +kernel
    exact cs16981b1all c (by omega : c < 5)
  · have : (R.getD 2 []).length = 32 := by decide +kernel
    exact cs16981b2all c (by omega : c < 1)
  · have : (R.getD 3 []).length = 40 := by decide +kernel
    exact cs16981b3all c (by omega : c < 2)
  · have : (R.getD 4 []).length = 2 := by decide +kernel
    exact cs16981b4all c (by omega : c < 1)

theorem chainHyp1 : ChainHyp SP SI T O PS B TL WD TR R 5 2 12 where
  lenO := by decide +kernel
  lenT := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h5 := by
    obtain ⟨h1', h2, h3, h4, -, -⟩ := gens_spec
    interval_cases i
    exacts [h1', h2, h3, h4]
  inv := gens_spec.2.2.2.2.1
  words := gens_spec.2.2.2.2.2
  tree i hi := (lvl_spec hi).2.1
  pos i hi := (lvl_spec hi).2.2
  cnt i hi := (lvl_spec hi).1
  blk i hi c hc := blk_spec hi c hc

end CFSG.KD.GUS1

end
