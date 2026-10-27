
module

public import CFSG.Fischer.Polar.DeltaBase
public import Certificates.Kernel.Misc.PolarMath
public import Certificates.Data.CFSGNative.Fischer.Polar
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv
import all CFSG.Fischer.F4

public section

namespace CFSG.KD.Misc.Polar

open CFSG.Fischer CFSG.Fischer.Native CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  Matrix

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  deltaTab

private theorem cube_one'' : ∀ c : F4, c ≠ 0 → c * c ^ 2 = 1 := by decide

local notation "M" g => (((g : GU0) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)

theorem uVec_smul_eq (g : GU0) (a : Fin 693) :
    ∃ c : F4, c ≠ 0 ∧ uVec ((g • a : Fin 693) : ℕ) = c • (M g).mulVec (uVec a) := by
  have hw := mulVec_ne_zero (g : GL (Fin 6) F4) (uVec_ne_zero ptsFacts a.2)
  have hi : hermStd ((M g).mulVec (uVec a)) ((M g).mulVec (uVec a)) = 0 := by
    rw [hermStd_mulVec]; exact uVec_iso ptsFacts a.2
  rw [smul_val, uVec_ptIdx ptsFacts hw hi]
  exact normV_eq_smul hw

theorem isPolarAut_piGU (g : GU0) : IsPolarAut (piGU g) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · change hermStd (uVec ((g • a : Fin 693) : ℕ)) (uVec ((g • b : Fin 693) : ℕ)) = 0 ↔ hermStd (uVec a) (uVec b) = 0
    obtain ⟨c, hc, ec⟩ := uVec_smul_eq g a
    obtain ⟨d, hd, ed⟩ := uVec_smul_eq g b
    rw [ec, ed, hermStd_smul_left, hermStd_smul_right, hermStd_mulVec]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hc
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) hd
        · exact h
    · intro h
      rw [h, mul_zero, mul_zero]
  · apply Fin.ext
    change (g • tvP a b).val = (tvP (g • a) (g • b)).val
    obtain ⟨c, hc, ec⟩ := uVec_smul_eq g a
    obtain ⟨d, hd, ed⟩ := uVec_smul_eq g b
    rw [smul_val, uVec_tvP, tvP_val, ec, ed]
    have hw := mulVec_ne_zero (tvGL (uVec a) (uVec_iso ptsFacts a.2)) (uVec_ne_zero ptsFacts b.2)
    rw [tvGL_val] at hw
    obtain ⟨e, he, ee⟩ := normV_eq_smul hw
    rw [ee, mulVec_smul, ptIdx_smul he, tvM_mulVec, mulVec_add, mulVec_smul,
      hermStd_smul_left, hermStd_smul_right, hermStd_mulVec, smul_smul]
    have : d * (c ^ 2 * hermStd (uVec b) (uVec a)) * c =
        d * (hermStd (uVec b) (uVec a) * (c * c ^ 2)) := by ring
    rw [this, cube_one'' c hc, mul_one, ← smul_smul, ← smul_add, ptIdx_smul hd]

private theorem pow6 : ∀ c : F4, c ≠ 0 → c ^ 6 = 1 := by decide

private theorem omega_step (i : Fin 3) : ∀ x : F4, F4.ω * x = F4.ω ^ ((i + 1 : Fin 3) : ℕ) ↔
    x = F4.ω ^ (i : ℕ) := by
  fin_cases i <;> decide

theorem uVec_delta (p : Fin 693) : ∃ c : F4, c ≠ 0 ∧
    ∀ k, uVec (delta p : ℕ) k = c * ((if k = 0 then F4.ω else 1) * uVec p k) := by
  obtain ⟨c, hc, ec⟩ := uVec_smul_eq deltaGU p
  have hd : delta p = deltaGU • p := by rw [delta_eq]; rfl
  refine ⟨c, hc, fun k => ?_⟩
  rw [hd, ec, deltaGU_val, deltaM, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]

theorem delta_mem_hypRoot (i : Fin 3) (p : Fin 693) :
    delta p ∈ hypRoot (i + 1) ↔ p ∈ hypRoot i := by
  obtain ⟨c, hc, ec⟩ := uVec_delta p
  have hw : weight (uVec (delta p : ℕ)) = weight (uVec p) := by
    unfold weight
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ec]
    split_ifs <;> simp [hc, F4.ω_ne_zero]
  have hprod : ∏ k, uVec (delta p : ℕ) k = F4.ω * ∏ k, uVec p k := by
    rw [Finset.prod_congr rfl (fun k _ => ec k), Fin.prod_univ_six, Fin.prod_univ_six]
    simp only [Fin.isValue, ite_true, show (1 : Fin 6) ≠ 0 by decide, show (2 : Fin 6) ≠ 0 by decide,
      show (3 : Fin 6) ≠ 0 by decide, show (4 : Fin 6) ≠ 0 by decide,
      show (5 : Fin 6) ≠ 0 by decide, ite_false, one_mul]
    linear_combination (F4.ω * uVec p 0 * uVec p 1 * uVec p 2 * uVec p 3 * uVec p 4 * uVec p 5) *
      pow6 c hc
  change (weight _ = 2 ∨ (weight _ = 6 ∧ _ = _)) ↔ (weight _ = 2 ∨ (weight _ = 6 ∧ _ = _))
  rw [hw, hprod, omega_step]

theorem image_delta (i : Fin 3) : ⇑delta '' hypRoot i = hypRoot (i + 1) := by
  ext q
  rw [Set.mem_image_equiv]
  rw [← delta_mem_hypRoot i (delta.symm q), Equiv.apply_symm_apply]

theorem flagSet_inj {F G : Flags} (hF : F.size = 693) (hG : G.size = 693)
    (h : flagSet F = flagSet G) : F = G := by
  apply Array.ext (by rw [hF, hG])
  intro i hi hi'
  have e := Set.ext_iff.1 h ⟨i, hF ▸ hi⟩
  rw [mem_flagSet, mem_flagSet, getElem!_pos F i hi, getElem!_pos G i hi'] at e
  exact Bool.eq_iff_iff.2 e

theorem rootFlags_size (c : ℕ) : (rootFlags c).size = 693 := by unfold rootFlags; simp

theorem imgFlags_size (T : Table) (F : Flags) : (imgFlags T F).size = 693 := by
  unfold imgFlags; simp

theorem root_step (i : Fin 3) :
    rootFlags ((i + 1 : Fin 3).val + 1) = imgFlags (invT 693 (deltaTab ())) (rootFlags (i.val + 1)) := by
  apply flagSet_inj (rootFlags_size _) (imgFlags_size _ _)
  rw [flagSet_rootFlags, flagSet_imgFlags (rep_invT_of_rep (by norm_num) rep_deltaTab),
    flagSet_rootFlags, image_delta]

theorem delta_true : deltaCertificate () = true := by
  have rD := rep_deltaTab
  have hA : IsPolarAut delta := by rw [delta_eq]; exact isPolarAut_piGU deltaGU
  unfold deltaCertificate deltaTabOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨invOK_invT_of_rep (by norm_num) rD, ?_⟩, ?_⟩, root_step 0⟩, root_step 1⟩,
    root_step 2⟩
  · rw [allIn_eq_true]
    intro a _ ha
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by rw [rD a ha]; exact idx_lt _ ha, ?_⟩
    rw [allIn_eq_true]
    intro b _ hb
    rw [beq_iff_eq, ← delta_val ⟨a, ha⟩, ← delta_val ⟨b, hb⟩]
    apply Bool.eq_iff_iff.2
    rw [perpTab_spec, perpTab_spec (⟨a, ha⟩ : Fin 693) ⟨b, hb⟩, hA.map_perp]
  · rw [allIn_eq_true]
    intro p _ hp
    rw [allIn_eq_true]
    intro q _ hq
    rw [beq_iff_eq]
    have h1 : ap tvTabs[p]! q = (tvP ⟨p, hp⟩ ⟨q, hq⟩).val := by
      rw [rep_tvP ⟨p, hp⟩ q hq, idx_of_lt _ hq]; rfl
    have h2 := rep_tvP (delta ⟨p, hp⟩) (delta ⟨q, hq⟩).val (delta ⟨q, hq⟩).2
    rw [idx_of_lt _ (delta ⟨q, hq⟩).2] at h2
    rw [h1, ← delta_val, ← delta_val ⟨p, hp⟩, ← delta_val ⟨q, hq⟩, h2, hA.map_tvP]
    rfl

end CFSG.KD.Misc.Polar

end
