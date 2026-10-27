
module

public import Certificates.Kernel.GammaU.Census0OK
public import Certificates.Kernel.GammaU.Census1OK
public import CFSG.Certificates.Kernel.GammaUCensusSound
public import CFSG.Certificates.Kernel.IdxFourChainCard

set_option maxRecDepth 100000

public section

namespace CFSG.KC.GUC

open CFSG.KC.IF4C

theorem exists_isP_of_candOK {CG CGI FT FTi FC TH i X G : Nat}
    (h : candOK CG FT FTi FC TH i X G = true) (hi : i < 32) (hX : fld FC X < 32)
    (hCG : ∀ l < 160, mulP (look CG l) (look CGI l) = idP)
    (hT : mulP (look FT X) (look FTi X) = idP) (hTH : mulP TH (mulP TH TH) = idP) :
    ∀ g < 11, ∃ U, IsP U (look G g) := by
  obtain ⟨h1, h2, h3⟩ := candOK_spec h
  intro g hg
  by_cases g5 : g < 5
  · rw [h1 g g5]
    exact IsP.exists_of_mul (hCG _ (by omega))
  by_cases g10 : g < 10
  · obtain ⟨l, rfl⟩ : ∃ l, g = 5 + l := ⟨g - 5, by omega⟩
    rw [h2 l (by omega)]
    obtain ⟨U, hU⟩ := IsP.exists_of_mul hT
    obtain ⟨V, hV⟩ := IsP.exists_of_mul (hCG (5 * fld FC X + l) (by omega))
    exact ⟨U * (V * U⁻¹), IsP.mul hU (IsP.mul hV (IsP.inv hU hT))⟩
  · obtain rfl : g = 10 := by omega
    rw [h3]
    exact IsP.exists_of_mul hTH

end CFSG.KC.GUC

namespace CFSG.KD.GUC0

open CFSG.KC.IF4C CFSG.KC.GUC

theorem kgens_spec : (∀ i < 5, tlOK KSP KB KTL KN (i + 1) = true) ∧ invOK KSP KSI KN = true ∧
    wordsOK KSP KSI KN KWD 11 = true ∧ (∀ l < 11, look KSP l = look AG l) ∧
    candOK CG FT FTi FC TH 0 AR AG = true := by
  have h := cc16966a_kgens
  unfold kgens at h
  simp only [Bool.and_eq_true, allBelow_iff, Nat.beq_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem klvl_spec {i : Nat} (hi : i < 6) :
    cntOK KO KTL KR i = true ∧ treeOK KSP KT KO KTL KTR i = true ∧ posOK KT KO KPS KB i = true := by
  have h : klvl i = true := cc16966a_klvall i hi
  unfold klvl at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem kblk_spec {i : Nat} (hi : i < 6) (c : Nat) (hc : 32 * c < (KR.getD i []).length) :
    blkOK KSP KT KO KTL KR i c = true := by
  change kblk i c = true
  interval_cases i
  · have : (KR.getD 0 []).length = 66 := by decide +kernel
    exact cc16966a_k0all c (by omega : c < 3)
  · have : (KR.getD 1 []).length = 16 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966a_k1b0
  · have : (KR.getD 2 []).length = 21 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966a_k2b0
  · have : (KR.getD 3 []).length = 24 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966a_k3b0
  · have : (KR.getD 4 []).length = 16 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966a_k4b0
  · have : (KR.getD 5 []).length = 4 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966a_k5b0

theorem chainHyp : ChainHyp KSP KSI KT KO KPS KB KTL KWD KTR KR 6 11 KN where
  lenO := by decide +kernel
  lenT := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h6 := by
    have := kgens_spec.1 (i - 1) (by omega)
    rwa [Nat.sub_add_cancel h1] at this
  inv := kgens_spec.2.1
  words := kgens_spec.2.2.1
  tree i hi := (klvl_spec hi).2.1
  pos i hi := (klvl_spec hi).2.2
  cnt i hi := (klvl_spec hi).1
  blk i hi c hc := kblk_spec hi c hc

theorem lvlGrp_eq : lvlGrp KSP KTL 0 = lGrp AG 11 := by
  have h0 : KTL.getD 0 [] = List.range 11 := by decide +kernel
  unfold lvlGrp lGrp
  congr 1
  ext U
  simp only [h0, List.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hg, hU⟩
    exact ⟨g, hg, by rwa [← kgens_spec.2.2.2.1 g hg]⟩
  · rintro ⟨g, hg, hU⟩
    exact ⟨g, hg, by rwa [kgens_spec.2.2.2.1 g hg]⟩

theorem card_AG : Nat.card (lGrp AG 11) = 1152 := by
  rw [← lvlGrp_eq, chainHyp.card_zero]
  decide +kernel

theorem or_lt : ∀ q < 11, OR.getD q 0 < 384 := by decide +kernel

theorem card_OG : ∀ q < 11, Nat.card (lGrp (OG.getD q 0) 11) ≠ 1152 := by
  intro q hq
  have h := cc16966a_orball q hq
  unfold orb at h
  rw [Bool.and_eq_true, nthD_eq, nthD_eq, nthD_eq, nthD_eq, nthD_eq] at h
  have hinv := cc16966a_inv
  simp only [Bool.and_eq_true, Nat.beq_eq] at hinv
  have hlen := cc16966a_len
  simp only [Bool.and_eq_true, allBelow_iff, Nat.blt_eq] at hlen
  refine card_ne_of_orbOK h.2 (exists_isP_of_candOK h.1 (by norm_num)
    (hlen.2 _ (or_lt q hq)) (invOK_spec (h := hinv.1.2)) ?_ hinv.2)
  exact invOK_spec _ _ hinv.1.1.1 _ (or_lt q hq)

end CFSG.KD.GUC0

namespace CFSG.KD.GUC1

open CFSG.KC.IF4C CFSG.KC.GUC

theorem kgens_spec : (∀ i < 5, tlOK KSP KB KTL KN (i + 1) = true) ∧ invOK KSP KSI KN = true ∧
    wordsOK KSP KSI KN KWD 11 = true ∧ (∀ l < 11, look KSP l = look AG l) ∧
    candOK CG FT FTi FC TH 1 AR AG = true := by
  have h := cc16966b_kgens
  unfold kgens at h
  simp only [Bool.and_eq_true, allBelow_iff, Nat.beq_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem klvl_spec {i : Nat} (hi : i < 6) :
    cntOK KO KTL KR i = true ∧ treeOK KSP KT KO KTL KTR i = true ∧ posOK KT KO KPS KB i = true := by
  have h : klvl i = true := cc16966b_klvall i hi
  unfold klvl at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem kblk_spec {i : Nat} (hi : i < 6) (c : Nat) (hc : 32 * c < (KR.getD i []).length) :
    blkOK KSP KT KO KTL KR i c = true := by
  change kblk i c = true
  interval_cases i
  · have : (KR.getD 0 []).length = 66 := by decide +kernel
    exact cc16966b_k0all c (by omega : c < 3)
  · have : (KR.getD 1 []).length = 16 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966b_k1b0
  · have : (KR.getD 2 []).length = 21 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966b_k2b0
  · have : (KR.getD 3 []).length = 24 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966b_k3b0
  · have : (KR.getD 4 []).length = 12 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966b_k4b0
  · have : (KR.getD 5 []).length = 2 := by decide +kernel
    obtain rfl : c = 0 := by omega
    exact cc16966b_k5b0

theorem chainHyp : ChainHyp KSP KSI KT KO KPS KB KTL KWD KTR KR 6 11 KN where
  lenO := by decide +kernel
  lenT := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h6 := by
    have := kgens_spec.1 (i - 1) (by omega)
    rwa [Nat.sub_add_cancel h1] at this
  inv := kgens_spec.2.1
  words := kgens_spec.2.2.1
  tree i hi := (klvl_spec hi).2.1
  pos i hi := (klvl_spec hi).2.2
  cnt i hi := (klvl_spec hi).1
  blk i hi c hc := kblk_spec hi c hc

theorem lvlGrp_eq : lvlGrp KSP KTL 0 = lGrp AG 11 := by
  have h0 : KTL.getD 0 [] = List.range 11 := by decide +kernel
  unfold lvlGrp lGrp
  congr 1
  ext U
  simp only [h0, List.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hg, hU⟩
    exact ⟨g, hg, by rwa [← kgens_spec.2.2.2.1 g hg]⟩
  · rintro ⟨g, hg, hU⟩
    exact ⟨g, hg, by rwa [kgens_spec.2.2.2.1 g hg]⟩

theorem card_AG : Nat.card (lGrp AG 11) = 1152 := by
  rw [← lvlGrp_eq, chainHyp.card_zero]
  decide +kernel

theorem or_lt : ∀ q < 11, OR.getD q 0 < 384 := by decide +kernel

theorem card_OG : ∀ q < 11, Nat.card (lGrp (OG.getD q 0) 11) ≠ 1152 := by
  intro q hq
  have h := cc16966b_orball q hq
  unfold orb at h
  rw [Bool.and_eq_true, nthD_eq, nthD_eq, nthD_eq, nthD_eq, nthD_eq] at h
  have hinv := cc16966b_inv
  simp only [Bool.and_eq_true, Nat.beq_eq] at hinv
  have hlen := cc16966b_len
  simp only [Bool.and_eq_true, allBelow_iff, Nat.blt_eq] at hlen
  refine card_ne_of_orbOK h.2 (exists_isP_of_candOK h.1 (by norm_num)
    (hlen.2 _ (or_lt q hq)) (invOK_spec (h := hinv.1.2)) ?_ hinv.2)
  exact invOK_spec _ _ hinv.1.1.1 _ (or_lt q hq)

end CFSG.KD.GUC1

end
