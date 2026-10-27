module

public import CFSG.Certificates.Kernel.E6TwA2Sound
public import Certificates.Kernel.E6TwA2.Roots

public section

namespace CertificateChecks.KernelE6TwA2

open Certificates.E6TwA2K CFSG.KC.E6TwA2 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint

@[expose] def PlaneOK (S : (Fin Tag.E6.rank → ℤ) → Prop) : Prop :=
  (∀ α, IsRoot Tag.E6 α → ¬ S α) →
    ∃ β₁ β₂ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β₁ ∧ IsRoot Tag.E6 β₂ ∧
      IsRoot Tag.E6 (β₁ + β₂) ∧ S (β₁ - β₂) ∧ ∃ δ, S δ ∧ ¬ (3 : ℤ) ∣ iform δ (β₁ + β₂)

@[expose] def kerS (x y z : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) : Prop :=
  triPairing x v = 0 ∧ triPairing y v = 0 ∧ triPairing z v = 0

theorem planeOK_congr {S T : (Fin Tag.E6.rank → ℤ) → Prop} (h : ∀ v, S v ↔ T v)
    (hS : PlaneOK S) : PlaneOK T := by
  have e : S = T := funext fun v => propext (h v)
  rwa [← e]

theorem reflect_add' (i : Fin Tag.E6.rank) (u v : Fin Tag.E6.rank → ℤ) :
    reflect .E6 i (u + v) = reflect .E6 i u + reflect .E6 i v := by
  simp only [reflect, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
  abel

theorem reflect_sub' (i : Fin Tag.E6.rank) (u v : Fin Tag.E6.rank → ℤ) :
    reflect .E6 i (u - v) = reflect .E6 i u - reflect .E6 i v := by
  simp only [reflect, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_smul]
  abel


theorem planeOK_reflect (i : Fin Tag.E6.rank) {S : (Fin Tag.E6.rank → ℤ) → Prop}
    (h : PlaneOK fun v => S (reflect .E6 i v)) : PlaneOK S := by
  intro hS
  obtain ⟨β₁, β₂, h1, h2, h12, hd, δ, hδ, hf⟩ :=
    h fun α hα hSα => hS _ ((isRoot_reflect_iff i).2 hα) hSα
  refine ⟨reflect .E6 i β₁, reflect .E6 i β₂, (isRoot_reflect_iff i).2 h1,
    (isRoot_reflect_iff i).2 h2, ?_, ?_, reflect .E6 i δ, hδ, ?_⟩
  · rw [← reflect_add']
    exact (isRoot_reflect_iff i).2 h12
  · rw [← reflect_sub']
    exact hd
  · rw [← reflect_add', iform_reflect]
    exact hf

theorem triPairing_triReflect (i : Fin Tag.E6.rank) (b : Fin Tag.E6.rank → ZMod 3)
    (v : Fin Tag.E6.rank → ℤ) : triPairing (triReflect i b) v = triPairing b (reflect .E6 i v) := by
  have h := triChar_triReflect i b v
  rw [triChar_apply, triChar_apply, simple_smul] at h
  exact Z3.ofAdd_eq_ofAdd_iff.1 h

theorem planeOK_charAct (i : ℕ) {x y z : Fin Tag.E6.rank → ZMod 3}
    (h : PlaneOK (kerS (charAct x i) (charAct y i) (charAct z i))) : PlaneOK (kerS x y z) := by
  unfold charAct at h
  split_ifs at h with hi
  · refine planeOK_reflect ⟨i, hi⟩ (planeOK_congr (fun v => ?_) h)
    simp only [kerS, triPairing_triReflect]
  · exact h

theorem planeOK_foldl : ∀ (w : List ℕ) (x y z : Fin Tag.E6.rank → ZMod 3),
    PlaneOK (kerS (w.foldl charAct x) (w.foldl charAct y) (w.foldl charAct z)) →
      PlaneOK (kerS x y z)
  | [], _, _, _, h => h
  | i :: w, x, y, z, h => planeOK_charAct i (planeOK_foldl w _ _ _ h)

theorem triPairing_single' (b : Fin Tag.E6.rank → ZMod 3) (j : Fin Tag.E6.rank) :
    triPairing b (Pi.single j 1) = b j := by
  have h := triPairing_zsmul_single b 1 j
  rwa [one_smul, Int.cast_one, mul_one] at h

theorem triPairing_zero_left (v : Fin Tag.E6.rank → ℤ) :
    triPairing (0 : Fin Tag.E6.rank → ZMod 3) v = 0 := by
  simp [triPairing]

theorem charAct_ne_zero {x : Fin Tag.E6.rank → ZMod 3} (hx : x ≠ 0) (i : ℕ) : charAct x i ≠ 0 := by
  unfold charAct
  split_ifs with hi
  · intro h0
    apply hx
    funext j
    have h := triPairing_triReflect ⟨i, hi⟩ x (reflect .E6 ⟨i, hi⟩ (Pi.single j 1))
    rw [h0, reflect_reflect, triPairing_zero_left, triPairing_single'] at h
    exact h.symm
  · exact hx

theorem foldl_ne_zero : ∀ (w : List ℕ) {x : Fin Tag.E6.rank → ZMod 3}, x ≠ 0 →
    w.foldl charAct x ≠ 0
  | [], _, hx => hx
  | i :: w, _, hx => foldl_ne_zero w (charAct_ne_zero hx i)

theorem triPairing_two_mul {x x' : Fin Tag.E6.rank → ZMod 3} (h : ∀ j, x j = 2 * x' j)
    (v : Fin Tag.E6.rank → ℤ) : triPairing x v = 2 * triPairing x' v := by
  simp only [triPairing, h, mul_assoc, Finset.mul_sum]

theorem two_mul_eq_zero (a : ZMod 3) : 2 * a = 0 ↔ a = 0 := by
  revert a
  decide

theorem triPairing_norm {n : ℕ} (hn : n < 729) (v : Fin Tag.E6.rank → ℤ) :
    triPairing (vec3OfIndex (τ := .E6) n) v = 0 ↔
      triPairing (vec3OfIndex (τ := .E6) (normC n)) v = 0 := by
  rcases (normOK_sound ch214102_norm n hn).2 with h | h
  · rw [funext h]
  · rw [triPairing_two_mul h, two_mul_eq_zero]

theorem planeOK_norm {n : ℕ} (hn : n < 729)
    (h : ∀ y z, PlaneOK (kerS (vec3OfIndex (τ := .E6) (normC n)) y z)) (y z) :
    PlaneOK (kerS (vec3OfIndex (τ := .E6) n) y z) :=
  planeOK_congr (fun v => by simp only [kerS, triPairing_norm hn v]) (h y z)

theorem fld_RP {k : ℕ} (hk : k < 72) : fld RP 24 k = e6Certificate.roots.getD k 0 :=
  (rootsOK_sound ch214102_rootsE).2 k hk

theorem isRoot_fld {k : ℕ} (hk : k < 72) : IsRoot Tag.E6 (decodeVec (fld RP 24 k)) := by
  rw [fld_RP hk]
  exact RootCertificate.isRoot_root e6Certificate_check k
    ((rootsOK_sound ch214102_rootsE).1 ▸ hk)

theorem lt_729 {n : ℕ} (hn : n < 3 ^ Tag.E6.rank) : n < 729 := hn

theorem planeOK_class {p pp : ℕ} {ws : List (List ℕ)} (hp : normB p = true) (hpp : posOf p = pp)
    (hrecs : recsOK RP ws = true) (hrep : repOK pp ws = true) (y z : Fin Tag.E6.rank → ZMod 3) :
    PlaneOK (kerS (vec3OfIndex (τ := .E6) p) y z) := by
  obtain ⟨ny, hny, rfl⟩ := exists_vec3OfIndex (τ := .E6) y
  obtain ⟨nz, hnz, rfl⟩ := exists_vec3OfIndex (τ := .E6) z
  have hby := (normOK_sound ch214102_norm ny (lt_729 hny)).1
  have hbz := (normOK_sound ch214102_norm nz (lt_729 hnz)).1
  refine planeOK_congr (S := kerS (vec3OfIndex (τ := .E6) p)
    (vec3OfIndex (τ := .E6) (normC ny)) (vec3OfIndex (τ := .E6) (normC nz))) (fun v => ?_) ?_
  · simp only [kerS, triPairing_norm (lt_729 hny) v, triPairing_norm (lt_729 hnz) v]
  have hrec := fun r (hr : r ∈ ws) => recOK_sound (recsOK_sound hrecs r hr)
  obtain ⟨r, hr, ⟨c1, hc1, e1⟩, ⟨c2, hc2, e2⟩, ⟨c3, hc3, e3⟩⟩ := repOK_sound hrep
    (fun r hr c hc => posOf_lt ((hrec r hr).1 c hc)) (posOf_lt hby) (posOf_lt hbz)
  have hn := (hrec r hr).1
  rw [posOf_inj (hn c1 hc1) hp (e1.trans hpp.symm)] at hc1
  rw [posOf_inj (hn c2 hc2) hby e2] at hc2
  rw [posOf_inj (hn c3 hc3) hbz e3] at hc3
  intro hS
  rcases (hrec r hr).2 with ⟨-, hi1, hk⟩ | ⟨-, hi1, hi2, hi3, hsum, hform, hk⟩
  · exact absurd ⟨hk _ hc1, hk _ hc2, hk _ hc3⟩ (hS _ (isRoot_fld hi1))
  · refine ⟨decodeVec (fld RP 24 (hd (tl r))), decodeVec (fld RP 24 (hd (tl (tl r)))),
      isRoot_fld hi1, isRoot_fld hi2, ?_, ⟨(hk _ hc1).1, (hk _ hc2).1, (hk _ hc3).1⟩,
      digLift (hd (tl (tl (tl (tl r))))), ⟨(hk _ hc1).2, (hk _ hc2).2, (hk _ hc3).2⟩, ?_⟩
    · rw [hsum]
      exact isRoot_fld hi3
    · rw [hsum]
      exact hform

theorem reps_eq : reps = [0, 1, 2, 3, 4, 8, 13, 27] := eq_of_beq ch214102_reps

theorem planeOK_rep {r : ℕ} (hr : r ∈ reps) (h0 : r ≠ 0) (y z : Fin Tag.E6.rank → ZMod 3) :
    PlaneOK (kerS (vec3OfIndex (τ := .E6) r) y z) := by
  have c1 := planeOK_class (p := 1) rfl rfl ch214102_recs0 ch214102_rep0
  have c3 := planeOK_class (p := 3) rfl rfl ch214102_recs1 ch214102_rep1
  have c4 := planeOK_class (p := 4) rfl rfl ch214102_recs2 ch214102_rep2
  have c13 := planeOK_class (p := 13) rfl rfl ch214102_recs3 ch214102_rep3
  have c27 := planeOK_class (p := 27) rfl rfl ch214102_recs4 ch214102_rep4
  rw [reps_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · exact c1 y z
  · have e : normC 2 = 1 := rfl
    exact planeOK_norm (by norm_num) (by rw [e]; exact c1) y z
  · exact c3 y z
  · exact c4 y z
  · have e : normC 8 = 4 := rfl
    exact planeOK_norm (by norm_num) (by rw [e]; exact c4) y z
  · exact c13 y z
  · exact c27 y z

theorem vec3OfIndex_zero : vec3OfIndex (τ := .E6) 0 = 0 := by
  funext j
  simp [vec3OfIndex]

theorem planeOK_ne_zero (x y z : Fin Tag.E6.rank → ZMod 3) (hx : x ≠ 0) :
    PlaneOK (kerS x y z) := by
  obtain ⟨n, hn, rfl⟩ := exists_vec3OfIndex (τ := .E6) x
  have hwl : wd.length = 729 := by decide +kernel
  have hmem := wordsOK_sound ch214102_words n (hwl ▸ lt_729 hn)
  refine planeOK_foldl (wd.getD n []) _ _ _ ?_
  rw [← applyW_spec]
  refine planeOK_rep hmem (fun h0 => foldl_ne_zero (wd.getD n []) hx ?_) _ _
  rw [← applyW_spec, h0, vec3OfIndex_zero]

theorem e6TwA2_plane : ∀ x y z : Fin Tag.E6.rank → ZMod 3,
    (∀ α, IsRoot Tag.E6 α → triPairing x α = 0 → triPairing y α = 0 → triPairing z α ≠ 0) →
    ∃ β₁ β₂ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β₁ ∧ IsRoot Tag.E6 β₂ ∧
      IsRoot Tag.E6 (β₁ + β₂) ∧ triPairing x (β₁ - β₂) = 0 ∧ triPairing y (β₁ - β₂) = 0 ∧
      triPairing z (β₁ - β₂) = 0 ∧
      ∃ δ : Fin Tag.E6.rank → ℤ, triPairing x δ = 0 ∧ triPairing y δ = 0 ∧
        triPairing z δ = 0 ∧ ¬ (3 : ℤ) ∣ iform δ (β₁ + β₂) := by
  intro x y z hreg
  have key : PlaneOK (kerS x y z) := by
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · by_cases hz : z = 0
        · intro hS
          refine absurd ?_ (hS _ (IsRoot.basis ⟨0, by decide⟩))
          rw [hx, hy, hz]
          exact ⟨triPairing_zero_left _, triPairing_zero_left _, triPairing_zero_left _⟩
        · exact planeOK_congr (fun v => by simp only [kerS]; tauto) (planeOK_ne_zero z x y hz)
      · exact planeOK_congr (fun v => by simp only [kerS]; tauto) (planeOK_ne_zero y x z hy)
    · exact planeOK_ne_zero x y z hx
  obtain ⟨β₁, β₂, h1, h2, h12, ⟨d1, d2, d3⟩, δ, ⟨e1, e2, e3⟩, hf⟩ :=
    key fun α hα ⟨a, b, c⟩ => hreg α hα a b c
  exact ⟨β₁, β₂, h1, h2, h12, d1, d2, d3, δ, e1, e2, e3, hf⟩

end CertificateChecks.KernelE6TwA2

end
