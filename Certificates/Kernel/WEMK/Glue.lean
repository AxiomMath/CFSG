module

public import Certificates.Kernel.WEMK.Checks
public import CFSG.Certificates.Kernel.WEMKSound

public section

namespace CFSG.StandardType.ZS.WEMK

open Certificates.ExcModel Certificates.WEMK CFSG.KD.WEMK

theorem covN_gens {n : ℕ} {S : List NMat} {V : List KPair} {cov : List ℕ} (Sm : List (M13 n)) (gens : Set (Mat n))
    (hSm : ∀ s ∈ Sm, s.val ∈ gens) (hgS : ∀ g ∈ gens, ∃ s ∈ Sm, s.val = g)
    (h : kCovN n S (Sm.map toN) V cov = true) :
    (∀ s < S.length, toM n (S.getD s []) ∈ gens) ∧ (∀ g ∈ gens, ∃ i < V.length, Lm n V i = g) ∧
      ∀ s0 ∈ Sm.head?, toM n (S.getD 0 []) = s0.val := by
  obtain ⟨hSG, hj⟩ := kCovN_sound h
  subst hSG
  have hget : ∀ c (hc : c < Sm.length), toM n ((Sm.map toN).getD c []) = (Sm[c]'hc).val := fun c hc => by
    rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, toM_toN]
  refine ⟨fun s hs => ?_, fun g hg => ?_, fun s0 hs0 => ?_⟩
  · have hs' : s < Sm.length := by simpa using hs
    rw [hget s hs']
    exact hSm _ (List.getElem_mem hs')
  · obtain ⟨s, hs, rfl⟩ := hgS g hg
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hs
    obtain ⟨i, hi, e⟩ := hj c (by simpa using hc)
    exact ⟨i, hi, by rw [e, hget c hc]⟩
  · cases Sm with
    | nil => simp at hs0
    | cons a l =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hs0
      subst hs0
      rw [hget 0 (by simp)]
      rfl

theorem wit_n4 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (f : ↥(glClosure n4Gens) ≃* ↥A)
    (hf : ∀ g : ↥(glClosure n4Gens), IsReflMat (g : owEm_GL 4) ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) : ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  have h := Bool.and_eq_true_iff.mp n4_ok
  obtain ⟨hSg, hgX, h0⟩ := covN_gens (n4S ()) n4Gens (by
      intro s hs
      simp only [n4S, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [n4Gens, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hs with rfl | rfl | rfl | rfl <;> simp [owEm_strict]) (by
      intro g hg
      simp only [n4Gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact ⟨strict (piMat 0 1 1), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 1 2 1), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 0 1 5), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict aMat, by simp [n4S], owEm_strict _⟩) h.2
  refine kRow_wit N4.S N4.V N4.tab N4.par N4.wd N4.x0 N4.t0 N4.tr N4.ord h.1 (by decide +kernel) n4Gens hSg hgX
    ?_ f hf hone
  intro g hg hgg
  have hg' : (g : Mat 4) = piMat 0 1 1 := by rw [hg, h0 (strict (piMat 0 1 1)) (by simp [n4S]), owEm_strict]
  exact owEm_isReflMat_of_outer g hgg ![1, -1, 0, 0] ![-1, 1, 0, 0] (by decide) (by decide)
    (by rw [hg']; exact owEm_piMat_sub_one)

theorem wit_en4 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (f : ↥(glClosure en4Gens) ≃* ↥A)
    (hf : ∀ g : ↥(glClosure en4Gens), IsReflMat (g : owEm_GL 4) ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) : ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  have h := Bool.and_eq_true_iff.mp en4_ok
  obtain ⟨hSg, hgX, h0⟩ := covN_gens (en4S ()) en4Gens (by
      intro s hs
      simp only [en4S, n4S, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [en4Gens, n4Gens, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hs with (rfl | rfl | rfl | rfl) | rfl
      · exact Or.inl (Or.inl (owEm_strict _))
      · exact Or.inl (Or.inr (Or.inl (owEm_strict _)))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (owEm_strict _))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (owEm_strict _))))
      · exact Or.inr (owEm_strict _)) (by
      intro g hg
      simp only [en4Gens, n4Gens, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with (rfl | rfl | rfl | rfl) | rfl
      · exact ⟨strict (piMat 0 1 1), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 1 2 1), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 0 1 5), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict aMat, by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (Matrix.diagonal fun i => if i = 3 then -1 else 1),
          by unfold en4S; exact List.mem_append_right _ (List.mem_singleton_self _), owEm_strict _⟩) h.2
  refine kRow_wit EN4.S EN4.V EN4.tab EN4.par EN4.wd EN4.x0 EN4.t0 EN4.tr EN4.ord h.1 (by decide +kernel) en4Gens
    hSg hgX ?_ f hf hone
  intro g hg hgg
  have hg' : (g : Mat 4) = piMat 0 1 1 := by rw [hg, h0 (strict (piMat 0 1 1)) (by simp [en4S, n4S]), owEm_strict]
  exact owEm_isReflMat_of_outer g hgg ![1, -1, 0, 0] ![-1, 1, 0, 0] (by decide) (by decide)
    (by rw [hg']; exact owEm_piMat_sub_one)

theorem wit_k6 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (f : ↥(glClosure k6Gens) ≃* ↥A)
    (hf : ∀ g : ↥(glClosure k6Gens), IsReflMat (g : owEm_GL 6) ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) : ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  have h := Bool.and_eq_true_iff.mp k6_ok
  obtain ⟨hR, hS⟩ := kCovK_gens (ctList ()) h.2
  refine kRow_wit K6.S K6.V K6.tab K6.par K6.wd K6.x0 K6.t0 K6.tr K6.ord h.1 (by decide +kernel) k6Gens
    (fun s hs => ?_) (fun g hg => ?_) (fun g hg hgg => ?_) f hf hone
  · obtain ⟨w, hw, e⟩ := hS s hs
    exact ⟨w, owEm_ctList_sound w hw, e⟩
  · obtain ⟨w, hw, rfl⟩ := hg
    exact hR w (owEm_ctList_complete w hw)
  · obtain ⟨w, hw, e⟩ := hS 0 (by decide +kernel)
    exact owEm_herRefl_isReflMat w hw g (by rw [hg, e]) hgg

theorem wit_k5 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (f : ↥(glClosure k5Gens) ≃* ↥A)
    (hf : ∀ g : ↥(glClosure k5Gens), IsReflMat (g : owEm_GL 6) ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) : ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  have h := Bool.and_eq_true_iff.mp k5_ok
  obtain ⟨hR, hS⟩ := kCovK_gens ((ctList ()).filter fun w => decide (w.1 0 - w.1 1 = 0)) h.2
  refine kRow_wit K5.S K5.V K5.tab K5.par K5.wd K5.x0 K5.t0 K5.tr K5.ord h.1 (by decide +kernel) k5Gens
    (fun s hs => ?_) (fun g hg => ?_) (fun g hg hgg => ?_) f hf hone
  · obtain ⟨w, hw, e⟩ := hS s hs
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    exact ⟨w, owEm_ctList_sound w hw.1, hw.2, e⟩
  · obtain ⟨w, hw, h0, rfl⟩ := hg
    exact hR w (by simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨owEm_ctList_complete w hw, h0⟩)
  · obtain ⟨w, hw, e⟩ := hS 0 (by decide +kernel)
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    exact owEm_herRefl_isReflMat w hw.1 g (by rw [hg, e]) hgg

theorem wemk_wit : ∀ (k : ExcRow), k.needsModel → ∀ {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)}, OneClass p A → ModelIso p k A → ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  intro k hk p U _ _ A hone hmod
  obtain ⟨f, hf⟩ := hmod
  cases k with
  | N4 => exact wit_n4 f hf hone
  | EN4 => exact wit_en4 f hf hone
  | K5 => exact wit_k5 f hf hone
  | K6 => exact wit_k6 f hf hone
  | H4 => exact hk.elim
  | H3 => exact hk.elim
  | J34 => exact hk.elim
  | J35 => exact hk.elim
  | EJ35 => exact hk.elim
  | J44 => exact hk.elim

end CFSG.StandardType.ZS.WEMK

end
