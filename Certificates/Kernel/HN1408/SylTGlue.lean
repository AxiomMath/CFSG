module

public import Certificates.Kernel.HN1408.SylTFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SylTG

open Subgroup CFSG.KS CFSG.KS.Raw CFSG.KS.BaseMask CFSG.KS.PEnum CFSG.KC.Enum
open scoped commutatorElement

theorem distinct_spec {cnt len : ℕ} {I : ℕ → ℕ} (h : distinctK cnt I 0 len = true) :
    (∀ e < len, r32 I e < cnt) ∧ ∀ a < len, ∀ b < len, r32 I a = r32 I b → a = b := by
  unfold distinctK at h
  rw [Nat.blt_eq, Orb.foldN_eq] at h
  obtain ⟨hd1, hd2, -⟩ := bmS_dist cnt (fun e => r32 I (0 + e)) _
    (fun e M => by rw [Orb.strictN_eq, Orb.nIf_eq, Orb.hasBit_eq]; rfl) _ h
  refine ⟨fun e he => ?_, fun a ha b hb hab => ?_⟩
  · have h1 := hd1 e (List.mem_range.2 he)
    rwa [Nat.zero_add] at h1
  · refine hd2 a (List.mem_range.2 ha) b (List.mem_range.2 hb) ?_
    beta_reduce
    rw [Nat.zero_add, Nat.zero_add]
    exact hab

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {R : Subgroup G} [Finite R] {s : G}
    (h : ∀ r ∈ R, s * r * s⁻¹ ∈ R) : s ∈ Subgroup.normalizer (R : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun r => ⟨h r, fun hr => ?_⟩
  let f : R → R := fun x => ⟨s * x * s⁻¹, h x x.2⟩
  have hf : Function.Injective f := fun a b e => by
    have := congrArg Subtype.val e
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨r', hr'⟩ := Finite.injective_iff_surjective.1 hf ⟨s * r * s⁻¹, hr⟩
  have e := congrArg Subtype.val hr'
  simp only [f, mul_left_inj, mul_right_inj] at e
  exact e ▸ r'.2

theorem commutator_le_of_gens {G : Type*} [Group G] {S D : Subgroup G} {s : Set G}
    (hS : S = Subgroup.closure s) (hN : ∀ x ∈ S, ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (hc : ∀ a ∈ s, ∀ b ∈ s, ⁅a, b⁆ ∈ D) : ⁅S, S⁆ ≤ D := by
  subst hS
  have step1 : ∀ b ∈ s, ∀ x ∈ Subgroup.closure s, ⁅x, b⁆ ∈ D := by
    intro b hb x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hc y hy b hb
    | one => simp [D.one_mem]
    | mul y z hy hz ihy ihz =>
      have e : ⁅y * z, b⁆ = y * ⁅z, b⁆ * y⁻¹ * ⁅y, b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (hN y hy _ ihz) ihy
    | inv y hy ihy =>
      have e : ⁅y⁻¹, b⁆ = y⁻¹ * (⁅y, b⁆)⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hN y⁻¹ (inv_mem hy) _ (inv_mem ihy)
  have step2 : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, ⁅x, y⁆ ∈ D := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem b hb => exact step1 b hb x hx
    | one => simp [D.one_mem]
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      have e : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem ih₁ (hN y₁ hy₁ _ ih₂)
    | inv y hy ih =>
      have e : ⁅x, y⁻¹⁆ = y⁻¹ * (⁅x, y⁆)⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hN y⁻¹ (inv_mem hy) _ (inv_mem ih)
  exact Subgroup.commutator_le.2 step2

end CFSG.KD.HN1408.SylTG

namespace CFSG.KD.HN1408.SylSG.RecS

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.BaseMask
  CFSG.KS.RecGroup CFSG.KD.HN1408 CFSG.KD.HN1408.SylSG CFSG.KD.HN1408.SylT CFSG.KS.MulH
  CFSG.KC.BfsPin CFSG.KD.HN1408.SylTF CFSG.KD.HN1408.SylTG
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

variable {x : ℕ → Equiv.Perm (Fin 1408)} (R : RecS x)
include R

theorem sub_mem {E PL C G : ℕ → ℕ} {ng cnt : ℕ} (h : subK E PL C G ng cnt = true)
    (hc : 0 < cnt) :
    (∀ e < cnt, r32 E e < 2048) ∧ (∀ t < ng, r32 G t < 2048) ∧
      (∀ a < cnt, ∀ b < cnt, x (r32 E a) = x (r32 E b) → a = b) ∧
      ∀ y, y ∈ closure ((fun t => x (r32 G t)) '' {t | t < ng}) ↔ ∃ e < cnt, x (r32 E e) = y := by
  unfold subK at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, hd, hg, hrows⟩ := h
  obtain ⟨hlt, hinj⟩ := distinct_spec hd
  have hglt : ∀ t < ng, r32 G t < 2048 := fun t ht => Nat.blt_eq.mp (Orb.allN_iff.1 hg t ht)
  have hrow := fun e (he : e < cnt) => Orb.allN_iff.1 hrows e he
  have hE0 : r32 E 0 = 0 := Nat.eq_of_beq_eq_true h0
  refine ⟨hlt, hglt, fun a ha b hb e => hinj a ha b hb (R.inj _ (hlt a ha) _ (hlt b hb) e), ?_⟩
  refine mem_closure_iff_of_right_record (x := fun e => x (r32 E e)) hc
    (by beta_reduce; rw [hE0, R.one]) ?_ ?_
  · intro e he0 he
    have h1 := hrow e he
    rw [Orb.strictB_eq, Bool.and_eq_true, Orb.bIf_eq,
      if_neg fun hb => absurd (Nat.eq_of_beq_eq_true hb) (by omega)] at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨hp, ht, hm⟩, -⟩ := h1
    have hp' : parF PL e < e := Nat.blt_eq.mp hp
    have ht' : labF PL e < ng := Nat.blt_eq.mp ht
    exact ⟨_, hp', _, ht', (R.mul_of_key (hlt _ (by omega)) (hglt _ ht') (hlt e he) hm).symm⟩
  · intro e he t ht
    have h1 := hrow e he
    rw [Orb.strictB_eq, Bool.and_eq_true] at h1
    have h2 := Orb.allN_iff.1 h1.2 t ht
    rw [Orb.strictB_eq, Bool.and_eq_true] at h2
    have hq : r32 C (Nat.add (Nat.mul ng e) t) < cnt := Nat.blt_eq.mp h2.1
    exact ⟨_, hq, (R.mul_of_key (hlt e he) (hglt t ht) (hlt _ hq) h2.2).symm⟩

theorem sub1_parts : (∀ e < 128, r32 E1 e < 2048) ∧ (∀ t < 6, r32 G1 t < 2048) ∧
    (∀ a < 128, ∀ b < 128, x (r32 E1 a) = x (r32 E1 b) → a = b) ∧
    ∀ y, y ∈ closure ((fun t => x (r32 G1 t)) '' {t | t < 6}) ↔ ∃ e < 128, x (r32 E1 e) = y :=
  R.sub_mem sub1_ok (by norm_num)

theorem sub2_parts : (∀ e < 512, r32 E2 e < 2048) ∧ (∀ t < 8, r32 G2 t < 2048) ∧
    (∀ a < 512, ∀ b < 512, x (r32 E2 a) = x (r32 E2 b) → a = b) ∧
    ∀ y, y ∈ closure ((fun t => x (r32 G2 t)) '' {t | t < 8}) ↔ ∃ e < 512, x (r32 E2 e) = y :=
  R.sub_mem sub2_ok (by norm_num)

omit R in
theorem tpWords_length : tpWords.length = 6 := by decide

omit R in
theorem w0Extra_length : w0Extra.length = 2 := by decide

omit R in
theorem tpWords_letters : ∀ t < 6, lettersOK (tpWords.getD t []) = true := by decide

omit R in
theorem w0Extra_letters : ∀ k < 2, lettersOK (w0Extra.getD k []) = true := by decide

omit R in
theorem g1_parts : r32 G1 0 = r32 CI 1 ∧ r32 G1 1 = r32 CI 4 ∧ r32 G1 2 = r32 CI 7 ∧
    r32 G1 3 = r32 CI 13 ∧ r32 G1 4 = r32 CI 14 ∧ r32 G1 5 = r32 CI 19 ∧
    ∀ t < 6, SylS.T (r32 G1 t) = WK (tpWords.getD t []) := by
  have h := g1_ok
  unfold g1K at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5,
    fun t ht => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h6 t ht)⟩

omit R in
theorem g2_parts : (∀ t < 6, r32 G2 t = r32 G1 t) ∧ ∀ k < 2, r32 G2 (6 + k) < 2048 ∧
    SylS.T (r32 G2 (6 + k)) = WK (w0Extra.getD k []) ∧ halfB (r32 G2 (6 + k)) = true ∧
    SylT.mk (r32 G2 (6 + k)) (r32 G2 (6 + k)) 0 = true := by
  have h := g2_ok
  unfold g2K at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  refine ⟨fun t ht => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h.1 t ht), fun k hk => ?_⟩
  have h1 := Orb.allN_iff.1 h.2 k hk
  rw [Orb.strictB_eq] at h1
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h1
  exact ⟨Nat.blt_eq.mp h1.1, Nat.eq_of_beq_eq_true h1.2.1, h1.2.2.1, h1.2.2.2⟩

theorem ent_g1 {t : ℕ} (ht : t < 6) : x (r32 G1 t) = elemW (tpWords.getD t []) :=
  R.ent_word ((R.sub1_parts).2.1 t ht) (tpWords_letters t ht) (g1_parts.2.2.2.2.2.2 t ht)

theorem ent_g2 {t : ℕ} (ht : t < 8) : x (r32 G2 t) = elemW ((tpWords ++ w0Extra).getD t []) := by
  by_cases h6 : t < 6
  · rw [g2_parts.1 t h6, R.ent_g1 h6, List.getD_append _ _ _ _ (by rw [tpWords_length]; exact h6)]
  · obtain ⟨k, rfl⟩ : ∃ k, t = 6 + k := ⟨t - 6, by omega⟩
    have hk : k < 2 := by omega
    obtain ⟨hlt, hT, -, -⟩ := g2_parts.2 k hk
    rw [R.ent_word hlt (w0Extra_letters k hk) hT, List.getD_append_right _ _ _ _
      (by rw [tpWords_length]; omega), tpWords_length, Nat.add_sub_cancel_left]

theorem T'_eq : wordSubgroup tpWords = closure ((fun t => x (r32 G1 t)) '' {t | t < 6}) := by
  have e := image_getD tpWords
  rw [tpWords_length] at e
  rw [wordSubgroup, ← e]
  congr 1
  exact Set.image_congr fun t ht => (R.ent_g1 ht).symm

theorem W0_eq : wordSubgroup (tpWords ++ w0Extra) =
    closure ((fun t => x (r32 G2 t)) '' {t | t < 8}) := by
  have e := image_getD (tpWords ++ w0Extra)
  rw [List.length_append, tpWords_length, w0Extra_length] at e
  rw [wordSubgroup, ← e]
  congr 1
  exact Set.image_congr fun t ht => (R.ent_g2 ht).symm

theorem mem_T' (y : Equiv.Perm (Fin 1408)) :
    y ∈ wordSubgroup tpWords ↔ ∃ e < 128, x (r32 E1 e) = y := by
  rw [R.T'_eq]
  exact (R.sub1_parts).2.2.2 y

theorem mem_W0 (y : Equiv.Perm (Fin 1408)) :
    y ∈ wordSubgroup (tpWords ++ w0Extra) ↔ ∃ e < 512, x (r32 E2 e) = y := by
  rw [R.W0_eq]
  exact (R.sub2_parts).2.2.2 y

theorem conj_of_key {y a d : ℕ} (hy : y < 2048) (ha : a < 2048) (hd : d < 2048)
    (h : conjKeyK 11 (mask 11) 2 0 SylS.T y a d = true) : x y * x a = x d * x y := by
  unfold conjKeyK at h
  obtain ⟨h1, h2⟩ := bmS_beq_pair h
  refine R.eq_of_base (mul_mem (R.mem_S hy) (R.mem_S ha)) (mul_mem (R.mem_S hd) (R.mem_S hy))
    ?_ ?_
  · rw [← R.pair hy ha (p := 2) (by norm_num), h1, R.pair hd hy (p := 2) (by norm_num)]
  · rw [← R.pair hy ha (p := 0) (by norm_num), h2, R.pair hd hy (p := 0) (by norm_num)]

theorem comm_row {i j : ℕ} (hi : i < 5) (hj : j < 5) :
    r32 CI (5 * i + j) < 2048 ∧ x (r32 CI (5 * i + j)) = ⁅x (i + 1), x (j + 1)⁆ ∧
      x (r32 CI (5 * i + j)) ∈ wordSubgroup tpWords := by
  have row : ∀ i < 5, ∀ j < 5, r32 PI (5 * i + j) < 2048 ∧ r32 CI (5 * i + j) < 2048 ∧
      SylT.mk (i + 1) (j + 1) (r32 PI (5 * i + j)) = true ∧
      SylT.mk (r32 CI (5 * i + j)) (r32 PI (5 * j + i)) (r32 PI (5 * i + j)) = true ∧
      r32 CP (5 * i + j) < 128 ∧ r32 E1 (r32 CP (5 * i + j)) = r32 CI (5 * i + j) := by
    intro i hi j hj
    have h := Orb.allN_iff.1 (Orb.allN_iff.1 comm_ok i hi) j hj
    unfold commRowK at h
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, h3, h4, Nat.blt_eq.mp h5, Nat.eq_of_beq_eq_true h6⟩
  obtain ⟨hp, hc, h3, h4, h5, h6⟩ := row i hi j hj
  obtain ⟨hp', -, h3', -⟩ := row j hj i hi
  have e1 : x (i + 1) * x (j + 1) = x (r32 PI (5 * i + j)) :=
    R.mul_of_key (by omega) (by omega) hp h3
  have e2 : x (j + 1) * x (i + 1) = x (r32 PI (5 * j + i)) :=
    R.mul_of_key (by omega) (by omega) hp' h3'
  have e3 : x (r32 CI (5 * i + j)) * x (r32 PI (5 * j + i)) = x (r32 PI (5 * i + j)) :=
    R.mul_of_key hc hp' hp h4
  refine ⟨hc, ?_, (R.mem_T' _).2 ⟨_, h5, by rw [h6]⟩⟩
  rw [← e2, ← e1] at e3
  rw [commutatorElement_def, ← e3]
  group

theorem norm_gen {j : ℕ} (hj : j < 5) {d : Equiv.Perm (Fin 1408)}
    (hd : d ∈ wordSubgroup tpWords) : x (j + 1) * d * (x (j + 1))⁻¹ ∈ wordSubgroup tpWords := by
  have hgen : ∀ t < 6, x (j + 1) * x (r32 G1 t) * (x (j + 1))⁻¹ ∈ wordSubgroup tpWords := by
    intro t ht
    have h := Orb.allN_iff.1 (Orb.allN_iff.1 norm_ok j hj) t ht
    rw [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
    have hd' : r32 NC (Nat.add (Nat.mul 6 j) t) < 128 := Nat.blt_eq.mp h.1
    have e := R.conj_of_key (by omega) ((R.sub1_parts).2.1 t ht) ((R.sub1_parts).1 _ hd') h.2
    rw [e, mul_inv_cancel_right]
    exact (R.mem_T' _).2 ⟨_, hd', rfl⟩
  have hle : wordSubgroup tpWords ≤
      (wordSubgroup tpWords).comap (MulAut.conj (x (j + 1))).toMonoidHom := by
    conv_lhs => rw [R.T'_eq]
    rw [closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact hgen t ht
  exact hle hd

theorem S_eq : wordSubgroup sWords = closure ((fun j => x (j + 1)) '' {j | j < 5}) := by
  have e := image_getD sWords
  rw [sWords_length] at e
  rw [wordSubgroup, ← e]
  congr 1
  exact Set.image_congr fun j hj => (R.ent_gen hj).symm

theorem derived_eq : ⁅wordSubgroup sWords, wordSubgroup sWords⁆ = wordSubgroup tpWords := by
  have hfin : Finite ↥(wordSubgroup tpWords) := inferInstance
  have hle : wordSubgroup sWords ≤
      Subgroup.normalizer (wordSubgroup tpWords : Set (Equiv.Perm (Fin 1408))) := by
    rw [R.S_eq, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact mem_normalizer_of_conj_mem fun d hd => R.norm_gen hj hd
  refine le_antisymm (commutator_le_of_gens R.S_eq
    (fun s hs d hd => Subgroup.le_normalizer_iff.1 hle s hs d hd) ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    rw [← (R.comm_row hi hj).2.1]
    exact (R.comm_row hi hj).2.2
  · have hc : ∀ i < 5, ∀ j < 5, x (r32 CI (5 * i + j)) ∈
        ⁅wordSubgroup sWords, wordSubgroup sWords⁆ := by
      intro i hi j hj
      rw [(R.comm_row hi hj).2.1]
      exact Subgroup.commutator_mem_commutator (R.mem_S (by omega)) (R.mem_S (by omega))
    rw [R.T'_eq, closure_le]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := g1_parts
    change t < 6 at ht
    beta_reduce
    interval_cases t
    · rw [h0]; exact hc 0 (by norm_num) 1 (by norm_num)
    · rw [h1]; exact hc 0 (by norm_num) 4 (by norm_num)
    · rw [h2]; exact hc 1 (by norm_num) 2 (by norm_num)
    · rw [h3]; exact hc 2 (by norm_num) 3 (by norm_num)
    · rw [h4]; exact hc 2 (by norm_num) 4 (by norm_num)
    · rw [h5]; exact hc 3 (by norm_num) 4 (by norm_num)

theorem w0_eq : wordSubgroup (tpWords ++ w0Extra) =
    closure ((wordSubgroup tpWords : Set (Equiv.Perm (Fin 1408))) ∪
      {y | y ∈ wordSubgroup sWords ⊓ blocks1408 ∧ y ^ 2 = 1}) := by
  apply le_antisymm
  · rw [R.W0_eq, closure_le]
    rintro _ ⟨t, ht, rfl⟩
    change t < 8 at ht
    by_cases h6 : t < 6
    · refine subset_closure (Or.inl ?_)
      beta_reduce
      rw [g2_parts.1 t h6, R.T'_eq]
      exact subset_closure ⟨t, h6, rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, t = 6 + k := ⟨t - 6, by omega⟩
      obtain ⟨hlt, -, hh, hm⟩ := g2_parts.2 k (by omega)
      refine subset_closure (Or.inr ⟨mem_inf.2 ⟨R.mem_S hlt, (R.ent_blocks hlt).2 hh⟩, ?_⟩)
      rw [pow_two, R.mul_of_key hlt hlt (by norm_num) hm, R.one]
  · rw [closure_le]
    rintro y (hy | ⟨hy, hy2⟩)
    · rw [R.T'_eq] at hy
      rw [R.W0_eq]
      refine closure_mono ?_ hy
      rintro _ ⟨t, ht, rfl⟩
      have ht6 : t < 6 := ht
      refine ⟨t, by change t < 8; omega, ?_⟩
      beta_reduce
      rw [g2_parts.1 t ht6]
    · obtain ⟨hyS, hyE⟩ := mem_inf.1 hy
      obtain ⟨i, hi, rfl⟩ := (R.mem _).1 hyS
      by_cases hi0 : i = 0
      · subst hi0
        rw [R.one]
        exact one_mem _
      have hsq : x i * x i = x 0 := by
        rw [R.one, ← pow_two]
        exact hy2
      have hIM : hasBit ivMask i = true :=
        ((involMaskK_spec sylS_inv).2 i hi).2 ⟨hi0, R.key_of_mul hi hi (by norm_num) hsq⟩
      have hW0 := invW0_ok
      unfold invW0K at hW0
      rw [Orb.strictB_eq] at hW0
      have hW := Orb.allN_iff.1 hW0 i hi
      rw [Orb.bIf_eq, if_pos (by rw [Orb.bAnd_eq, hIM, (R.ent_blocks hi).1 hyE]; rfl)] at hW
      obtain ⟨e, he, hei⟩ := (hasBit_maskK _ _ _ _).1 hW
      rw [Nat.zero_add] at hei
      exact (R.mem_W0 _).2 ⟨e, he, by rw [hei]⟩

omit R in
theorem counts_parts : cntS (r32 SylS.FM 1) = 80 ∧ cntS (r32 SylS.FM 3) = 48 ∧
    cntE E1 128 (r32 SylS.FM 1) = 16 ∧ cntE E1 128 (r32 SylS.FM 2) = 32 ∧
    cntE E1 128 (r32 SylS.FM 3) = 16 ∧ cntE E2 512 (r32 SylS.FM 1) = 48 ∧
    cntE E2 512 (r32 SylS.FM 3) = 16 := by
  have h := counts_ok
  unfold countsK at h
  simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7⟩

theorem sq_iff {i y : ℕ} (hi : i < 2048) (hy : y < 2048) :
    SylT.mk i i y = true ↔ x i ^ 2 = x y :=
  ⟨fun h => by rw [pow_two]; exact R.mul_of_key hi hi hy h,
    fun h => R.key_of_mul hi hi hy (by rw [← pow_two]; exact h)⟩

theorem card_sqT {y : ℕ} (hy : y < 2048) :
    {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup sWords ⊓ blocks1408 ∧ g ^ 2 = x y}.ncard =
      cntS y := by
  have e : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup sWords ⊓ blocks1408 ∧ g ^ 2 = x y} =
      {g | (∃ i < 2048, x i = g) ∧ (g ∈ blocks1408 ∧ g ^ 2 = x y)} := by
    ext g
    simp only [Set.mem_setOf_eq, mem_inf, R.mem g, and_assoc]
  rw [e, cntS, cntN_eq]
  refine ncard_count R.inj _ _ fun i hi => ?_
  rw [Orb.bAnd_eq, Bool.and_eq_true, R.ent_blocks hi, R.sq_iff hi hy]

theorem card_sqE {E : ℕ → ℕ} {cnt y : ℕ} {H : Subgroup (Equiv.Perm (Fin 1408))}
    (hlt : ∀ e < cnt, r32 E e < 2048) (hinj : ∀ a < cnt, ∀ b < cnt, x (r32 E a) = x (r32 E b) → a = b)
    (hmem : ∀ g, g ∈ H ↔ ∃ e < cnt, x (r32 E e) = g) (hy : y < 2048) :
    {g : Equiv.Perm (Fin 1408) | g ∈ H ∧ g ^ 2 = x y}.ncard = cntE E cnt y := by
  have e : {g : Equiv.Perm (Fin 1408) | g ∈ H ∧ g ^ 2 = x y} =
      {g | (∃ e < cnt, x (r32 E e) = g) ∧ g ^ 2 = x y} := by
    ext g
    simp only [Set.mem_setOf_eq, hmem g]
  rw [e, cntE, cntN_eq]
  refine ncard_count (f := fun e => x (r32 E e)) hinj _ _ fun i hi => ?_
  rw [Orb.strictB_eq, R.sq_iff (hlt i hi) hy]

theorem card_T_a : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup sWords ⊓ blocks1408 ∧
    g ^ 2 = elemA}.ncard = 80 := by
  rw [← R.ent_a, R.card_sqT (R.fm_lt (by norm_num))]
  exact counts_parts.1

theorem card_T_az : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup sWords ⊓ blocks1408 ∧
    g ^ 2 = elemA * elemZ}.ncard = 48 := by
  rw [← R.ent_az, R.card_sqT (R.fm_lt (by norm_num))]
  exact counts_parts.2.1

theorem card_T'_a :
    {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧ g ^ 2 = elemA}.ncard = 16 := by
  rw [← R.ent_a, R.card_sqE R.sub1_parts.1 R.sub1_parts.2.2.1 R.mem_T' (R.fm_lt (by norm_num))]
  exact counts_parts.2.2.1

theorem card_T'_z :
    {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧ g ^ 2 = elemZ}.ncard = 32 := by
  rw [← R.ent_z, R.card_sqE R.sub1_parts.1 R.sub1_parts.2.2.1 R.mem_T' (R.fm_lt (by norm_num))]
  exact counts_parts.2.2.2.1

theorem card_T'_az :
    {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧ g ^ 2 = elemA * elemZ}.ncard = 16 := by
  rw [← R.ent_az, R.card_sqE R.sub1_parts.1 R.sub1_parts.2.2.1 R.mem_T' (R.fm_lt (by norm_num))]
  exact counts_parts.2.2.2.2.1

theorem card_W0_a : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup (tpWords ++ w0Extra) ∧
    g ^ 2 = elemA}.ncard = 48 := by
  rw [← R.ent_a, R.card_sqE R.sub2_parts.1 R.sub2_parts.2.2.1 R.mem_W0 (R.fm_lt (by norm_num))]
  exact counts_parts.2.2.2.2.2.1

theorem card_W0_az : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup (tpWords ++ w0Extra) ∧
    g ^ 2 = elemA * elemZ}.ncard = 16 := by
  rw [← R.ent_az, R.card_sqE R.sub2_parts.1 R.sub2_parts.2.2.1 R.mem_W0 (R.fm_lt (by norm_num))]
  exact counts_parts.2.2.2.2.2.2

end CFSG.KD.HN1408.SylSG.RecS

end
