module

public import Certificates.Kernel.HSMK.Checks
public import CFSG.Certificates.Kernel.HSMKSound
public import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
import all CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs

public section

namespace CFSG.StandardType.ZS.HSMK

open Certificates.ExcModel Certificates.WEMK Certificates.HSMK CFSG.KD.HSMK CFSG.StandardType.ZS.WEMK
open scoped Matrix

theorem tuple_of {m : ℕ} (T : List NMat) (hm : T.length = m) (h3 : 3 < m) (V : List KPair) (tab : List (List ℕ))
    (par : List (ℕ × ℕ)) (E : List (List ℕ)) (e : Fin m → Fin m → ℕ)
    (hE : ∀ i j : Fin m, e i j = (E.getD i []).getD j 0) (gens : Set (Mat 6))
    (hgen : kGen 6 T V tab par = true) (hrel : kRel 6 T E = true) (hext : kExtra 6 T = true)
    (hTg : ∀ s < T.length, toM 6 (T.getD s []) ∈ gens) (hgX : ∀ g ∈ gens, ∃ i < V.length, Lm 6 V i = g)
    (hrefl : ∀ g : owEm_GL 6, (g : Mat 6) = toM 6 (T.getD 0 []) → (g : Mat 6) * g = 1 → IsReflMat g) :
    ∃ t : Fin m → ↥(glClosure gens), ((∀ i j, (t i * t j) ^ e i j = 1) ∧
      (t ⟨2, by omega⟩ * t ⟨1, by omega⟩ * t ⟨2, by omega⟩ * t ⟨3, h3⟩) ^ 3 = 1) ∧
      Subgroup.closure (Set.range t) = ⊤ ∧ IsReflMat (t ⟨0, by omega⟩).1 ∧
      (glClosure gens = Subgroup.closure {g : owEm_GL 6 | ∃ s < T.length, (g : Mat 6) = toM 6 (T.getD s [])}) ∧
      ∀ q ∈ V, ∃ u ∈ glClosure gens, (u : Mat 6) = toM 6 (mat 6 q) := by
  obtain ⟨hSf, hM, hV⟩ := gen_sound hgen (by omega) gens hTg hgX
  have hlt : ∀ i : Fin m, (i : ℕ) < T.length := fun i => hm ▸ i.2
  have hinv : ∀ i : Fin m, toM 6 (T.getD i []) * toM 6 (T.getD i []) = 1 := fun i =>
    (hSf _ (getD_mem_of_lt (hlt i))).2
  let u : Fin m → owEm_GL 6 := fun i => owEm_unit _ (hinv i)
  have hu : ∀ i, (u i : Mat 6) = toM 6 (T.getD i []) := fun i => rfl
  have humem : ∀ i, u i ∈ glClosure gens := fun i => Subgroup.subset_closure (by
    change (u i : Mat 6) ∈ gens
    rw [hu]
    exact hTg i (hlt i))
  let t : Fin m → ↥(glClosure gens) := fun i => ⟨u i, humem i⟩
  have hT : ∀ s ∈ T, WF 6 s := fun s hs => (hSf s hs).1
  refine ⟨t, ⟨fun i j => ?_, ?_⟩, ?_, ?_, hM, hV⟩
  · apply Subtype.ext
    apply Units.ext
    have := rel_sound hrel hT i (hlt i) j (hlt j)
    rw [← hE] at this
    simpa [t, hu] using this
  · apply Subtype.ext
    apply Units.ext
    have := extra_sound hext hT (by omega)
    simpa [t, hu] using this
  · have himage : (glClosure gens).subtype '' Set.range t =
        {g : owEm_GL 6 | ∃ s < T.length, (g : Mat 6) = toM 6 (T.getD s [])} := by
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, hlt i, hu i⟩
      · rintro ⟨s, hs, e⟩
        refine ⟨t ⟨s, hm ▸ hs⟩, ⟨_, rfl⟩, Units.ext ?_⟩
        rw [e]
        rfl
    apply Subgroup.map_injective (f := (glClosure gens).subtype) Subtype.val_injective
    rw [MonoidHom.map_closure, himage, Subgroup.map_top, Subgroup.range_subtype]
    exact hM.symm
  · exact hrefl _ (hu _) (hinv _)

theorem uset_le {gens : Set (Mat 6)} {V : List KPair}
    (hV : ∀ q ∈ V, ∃ u ∈ glClosure gens, (u : Mat 6) = toM 6 (mat 6 q)) :
    Subgroup.closure (uset 6 V) ≤ glClosure gens := by
  rw [Subgroup.closure_le]
  rintro u ⟨q, hq, e⟩
  obtain ⟨u', hu', e'⟩ := hV q hq
  have : u = u' := Units.ext (by rw [e, e'])
  rw [SetLike.mem_coe, this]
  exact hu'

theorem k5_data :
    ∃ t : Fin 5 → ↥(glClosure k5Gens), ((∀ i j, (t i * t j) ^ kFiveExp i j = 1) ∧
      (t 2 * t 1 * t 2 * t 3) ^ 3 = 1) ∧ Subgroup.closure (Set.range t) = ⊤ ∧ IsReflMat (t 0).1 ∧
      (glClosure k5Gens = Subgroup.closure {g : owEm_GL 6 | ∃ s < K5.T.length, (g : Mat 6) = toM 6 (K5.T.getD s [])}) ∧
      ∀ q ∈ K5.V, ∃ u ∈ glClosure k5Gens, (u : Mat 6) = toM 6 (mat 6 q) := by
  have hg := Bool.and_eq_true_iff.mp k5_gen
  have hr := Bool.and_eq_true_iff.mp k5_rel
  obtain ⟨hR, hS⟩ := kCovK_gens ((ctList ()).filter fun w => decide (w.1 0 - w.1 1 = 0)) hg.2
  exact tuple_of K5.T k5_lens.1 (by norm_num) K5.V K5.tab K5.par hsE kFiveExp (by decide) k5Gens hg.1 hr.1 hr.2
    (fun s hs => by
      obtain ⟨w, hw, e⟩ := hS s hs
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      exact ⟨w, owEm_ctList_sound w hw.1, hw.2, e⟩)
    (fun g hg => by
      obtain ⟨w, hw, h0, rfl⟩ := hg
      exact hR w (by simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨owEm_ctList_complete w hw, h0⟩))
    (fun g hg hgg => by
      obtain ⟨w, hw, e⟩ := hS 0 (by decide +kernel)
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      exact owEm_herRefl_isReflMat w hw.1 g (by rw [hg, e]) hgg)

theorem k6_data :
    ∃ t : Fin 6 → ↥(glClosure k6Gens), ((∀ i j, (t i * t j) ^ kSixExp i j = 1) ∧
      (t 2 * t 1 * t 2 * t 3) ^ 3 = 1) ∧ Subgroup.closure (Set.range t) = ⊤ ∧ IsReflMat (t 0).1 ∧
      ∀ q ∈ K6.V, ∃ u ∈ glClosure k6Gens, (u : Mat 6) = toM 6 (mat 6 q) := by
  have hg := Bool.and_eq_true_iff.mp k6_gen
  have hr := Bool.and_eq_true_iff.mp k6_rel
  obtain ⟨hR, hS⟩ := kCovK_gens (ctList ()) hg.2
  obtain ⟨t, h1, h2, h3, -, h5⟩ := tuple_of K6.T k6_lens.1 (by norm_num) K6.V K6.tab K6.par hsE kSixExp
    (by decide) k6Gens hg.1 hr.1 hr.2
    (fun s hs => by
      obtain ⟨w, hw, e⟩ := hS s hs
      exact ⟨w, owEm_ctList_sound w hw, e⟩)
    (fun g hg => by
      obtain ⟨w, hw, rfl⟩ := hg
      exact hR w (owEm_ctList_complete w hw))
    (fun g hg hgg => by
      obtain ⟨w, hw, e⟩ := hS 0 (by decide +kernel)
      exact owEm_herRefl_isReflMat w hw g (by rw [hg, e]) hgg)
  exact ⟨t, h1, h2, h3, h5⟩

theorem k5_card : 51840 ≤ Nat.card (glClosure k5Gens) := by
  obtain ⟨-, -, -, -, -, hV⟩ := k5_data
  have hG : ∀ q ∈ K5.V, ∃ u : owEm_GL 6, (u : Mat 6) = toM 6 (mat 6 q) := fun q hq => by
    obtain ⟨u, -, e⟩ := hV q hq
    exact ⟨u, e⟩
  have hc := chain_sound K5.lv K5.V k5_chain hG
  rw [k5_lens.2] at hc
  exact le_trans (by norm_num) (hc.trans (Nat.card_mono (Set.toFinite _) (uset_le hV)))

theorem k6_card : 756 * 51840 ≤ Nat.card (glClosure k6Gens) := by
  obtain ⟨-, -, -, -, hM5, -⟩ := k5_data
  obtain ⟨-, -, -, -, hV⟩ := k6_data
  have hG : ∀ q ∈ K6.V, ∃ u : owEm_GL 6, (u : Mat 6) = toM 6 (mat 6 q) := fun q hq => by
    obtain ⟨u, -, e⟩ := hV q hq
    exact ⟨u, e⟩
  have hB : ∀ u ∈ glClosure k5Gens, (u : Mat 6) *ᵥ vecN 6 e12N = vecN 6 e12N := by
    rw [hM5]
    exact tfix_sound k5_fix (gen_wf (Bool.and_eq_true_iff.mp k5_gen).1)
  have hBΓ : glClosure k5Gens ≤ glClosure k6Gens := by
    refine Subgroup.closure_mono ?_
    intro g hg
    obtain ⟨w, hw, -, hgw⟩ := hg
    exact ⟨w, hw, hgw⟩
  have h := lev_card k6_orb hG _ _ (uset_le hV) hBΓ hB k5_card
  rwa [k6_lens.2] at h

theorem hsmk_five : ∃ t : Fin 5 → ↥(model .K5), HSFiveRel t ∧ Subgroup.closure (Set.range t) = ⊤ ∧
    ExcRow.K5.ord ≤ Nat.card (model .K5) ∧ IsReflMat (t 0).1 := by
  obtain ⟨t, hrel, hgen, hrefl, -, -⟩ := k5_data
  refine ⟨t, hrel, hgen, ?_, hrefl⟩
  have hK : ExcRow.K5.ord = 51840 := by decide
  rw [hK]
  exact k5_card

theorem hsmk_six : ∃ t : Fin 6 → ↥(model .K6), HSSixRel t ∧ Subgroup.closure (Set.range t) = ⊤ ∧
    ExcRow.K6.ord ≤ Nat.card (model .K6) ∧ IsReflMat (t 0).1 := by
  obtain ⟨t, hrel, hgen, hrefl, -⟩ := k6_data
  refine ⟨t, hrel, hgen, ?_, hrefl⟩
  have hK : ExcRow.K6.ord = 756 * 51840 := by decide
  rw [hK]
  exact k6_card

end CFSG.StandardType.ZS.HSMK

end
