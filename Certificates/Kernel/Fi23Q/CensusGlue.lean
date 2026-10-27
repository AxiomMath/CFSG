
module

public import Certificates.Kernel.Fi23Q.Gens
public import CFSG.Certificates.Kernel.Fi23Q.CensusSound
import Certificates.Kernel.Fi23Q.Rel
import Certificates.Kernel.Fi23Q.CensusAll
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CertificateChecks.KernelFi23Q

open CFSG.Sporadic.Fi23 CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KS.Pc3 CFSG.KS.Fi23Q
  CFSG.Perm CFSG.KS.Raw.Orb CFSG.KD.Fi23K
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base qG)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Words

variable {G : Type*} [Group G]

theorem prod_range_single (f : ℕ → G) {k : ℕ} :
    ∀ n, k < n → (∀ m < n, m ≠ k → f m = 1) → ((List.range n).map f).prod = f k
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hf => by
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · rw [prod_range_single f n h' (fun m hm hmk => hf m (by omega) hmk), hf n (by omega) (by omega),
        mul_one]
    · rw [List.prod_eq_one, one_mul]
      intro g hg
      simp only [List.mem_map, List.mem_range] at hg
      obtain ⟨m, hm, rfl⟩ := hg
      exact hf m (by omega) (by omega)

theorem dg_unit (k m : ℕ) : dg (4 ^ k) m = if m = k then 1 else 0 := by
  rw [dg_eq]
  rcases lt_trichotomy m k with h | rfl | h
  · rw [if_neg (by omega), Nat.pow_div h.le (by norm_num)]
    obtain ⟨d, hd⟩ : ∃ d, k - m = d + 1 := ⟨k - m - 1, by omega⟩
    rw [hd, pow_succ, Nat.mul_mod_left]
  · simp
  · rw [if_neg (by omega), Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)]

theorem nv_unit (x : ℕ → G) {k : ℕ} (hk : k < 13) : nv x 13 (4 ^ k) = x k := by
  unfold nv
  rw [prod_range_single _ 13 hk fun m _ hmk => by rw [dg_unit, if_neg hmk, pow_zero]]
  rw [dg_unit, if_pos rfl, pow_one]

theorem nv_zero (x : ℕ → G) : nv x 13 0 = 1 := by
  unfold nv
  apply List.prod_eq_one
  intro g hg
  simp only [List.mem_map, List.mem_range] at hg
  obtain ⟨m, -, rfl⟩ := hg
  rw [dg_eq, Nat.zero_div, Nat.zero_mod, pow_zero]

end Words

theorem wvH_eq (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) {u : List ℕ}
    (hu : ∀ c ∈ u, c < 13) {b : ℕ} (hb : b < 31671) :
    wv CFSG.KD.Fi23Q.H u b = idx 31671 (wd aE u) b :=
  wv_eq_of (P := fun r => r < 13) (fun r hr => hH r hr) u hu b hb

theorem eqH_rep
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) :
    EqHRep CFSG.KD.Fi23Q.H aE := by
  intro u v hu hv
  constructor
  · intro h
    apply eq_of_base
    intro t ht
    have e := eqH_spec h t ht
    rwa [wvH_eq aE hH hu (by omega), wvH_eq aE hH hv (by omega)] at e
  · intro h
    unfold eqH
    rw [CFSG.KS.PK.allN_iff]
    intro b hb
    have hb' : b < 31671 := Nat.lt_of_lt_of_le hb (by decide)
    rw [wvH_eq aE hH hu hb', wvH_eq aE hH hv hb', h]
    exact Nat.beq_refl _

theorem relK_parts : pcDataOK 13 CFSG.KD.Fi23Q.PW CFSG.KD.Fi23Q.CJ = true ∧
    relB CFSG.KD.Fi23Q.H 13 CFSG.KD.Fi23Q.PW CFSG.KD.Fi23Q.CJ = true := by
  have h := CFSG.KD.Fi23Q.relK_ok
  unfold CFSG.KD.Fi23Q.relK at h
  rwa [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h

theorem cj_index (i j : ℕ) : Nat.add (Nat.shiftLeft i (nat_lit 4)) j = 16 * i + j := by
  change i <<< 4 + j = 16 * i + j
  rw [Nat.shiftLeft_eq]
  omega

theorem pcRel
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) :
    PcRel aE 13 CFSG.KD.Fi23Q.PW CFSG.KD.Fi23Q.CJ := by
  obtain ⟨hd, hr⟩ := relK_parts
  have hE := eqH_rep aE hH
  unfold relB at hr
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff] at hr
  unfold pcDataOK at hd
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff,
    CFSG.KS.PK.strictB_eq] at hd
  obtain ⟨hc, hj⟩ := hr
  constructor
  · intro k hk
    obtain ⟨W1, W2⟩ := nwR_spec aE (vecOK_dg (hd.2 k hk).1)
    have hl : ∀ c ∈ [k, k, k], c < 13 := fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    have e := eqH_wd hE hl W2 (hc k hk)
    rw [W1] at e
    rw [← e]
    simp [wd, pow_three]
  · intro i j hij hj13
    have hi : i < 13 := by omega
    have hcj := (hd.2 i hi).2.2 j hj13
    have hrel := hj i hi j hj13
    simp only [CFSG.KS.PK.bIf_eq, Nat.blt_eq, hij, ↓reduceIte, CFSG.KS.PK.strictB_eq,
      CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, cj_index] at hcj hrel
    obtain ⟨C1, C2⟩ := nwR_spec aE (vecOK_dg hcj.1)
    have hl : ∀ c ∈ [j, i], c < 13 := fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    have hl' : ∀ c ∈ i :: nwR 13 (f32 CFSG.KD.Fi23Q.CJ (16 * i + j)), c < 13 := fun c hc => by
      rcases List.mem_cons.1 hc with h | h
      · omega
      · exact C2 c h
    have e := eqH_wd hE hl hl' hrel
    rw [wd_cons, wd_cons, wd_cons, wd_nil, mul_one, C1] at e
    rw [mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]

theorem elemAb
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) : ElemAb aE := by
  have hP := pcRel aE hH
  have hc : ∀ l < 5, ∀ l' < 5, l < l' → Commute (aE (8 + l)) (aE (8 + l')) := by
    intro l hl l' hl' hll
    have e := hP.conj (8 + l) (8 + l') (by omega) (by omega)
    rw [CFSG.KD.Fi23Q.cjA_unit l hl l' hl' hll, nv_unit _ (by omega)] at e
    have e' : aE (8 + l') * aE (8 + l) = aE (8 + l) * aE (8 + l') := by
      calc aE (8 + l') * aE (8 + l)
          = aE (8 + l) * ((aE (8 + l))⁻¹ * aE (8 + l') * aE (8 + l)) := by group
        _ = aE (8 + l) * aE (8 + l') := by rw [e]
    exact e'.symm
  refine ⟨fun l hl => ?_, fun l hl l' hl' => ?_⟩
  · rw [hP.cube _ (by omega), CFSG.KD.Fi23Q.pwA_zero l hl, nv_zero]
  · rcases lt_trichotomy l l' with h | rfl | h
    · exact hc l hl l' hl' h
    · exact Commute.refl _
    · exact (hc l' hl' l hl h).symm

theorem normA
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) : NormA aE := by
  have hP := pcRel aE hH
  have hA := elemAb aE hH
  intro k hk l hl
  by_cases hkl : k < 8 + l
  · exact ⟨_, by rw [hP.conj k (8 + l) hkl (by omega),
      nv_aOK aE (CFSG.KD.Fi23Q.cjA_ok k hk l hl hkl)]⟩
  · obtain ⟨l', rfl⟩ : ∃ l', k = 8 + l' := ⟨k - 8, by omega⟩
    refine ⟨dA (4 ^ (8 + l)), ?_⟩
    rw [← nv_aOK aE (CFSG.KD.Fi23Q.unitA_ok l hl), nv_unit aE (by omega), mul_assoc,
      (hA.comm l hl l' (by omega)).eq, inv_mul_cancel_left]

theorem nf_of_mem
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) {y : CFSG.Sporadic.Fi23.J}
    (hy : y ∈ Subgroup.closure (aE '' Set.Iio 13)) :
    ∃ u, vecOK 13 u = true ∧ nv aE 13 u = y := by
  have hd := relK_parts.1
  have hP := pcRel aE hH
  have hmul : ∀ a b : CFSG.Sporadic.Fi23.J, (∃ u, vecOK 13 u = true ∧ nv aE 13 u = a) →
      (∃ u, vecOK 13 u = true ∧ nv aE 13 u = b) → ∃ u, vecOK 13 u = true ∧ nv aE 13 u = a * b := by
    rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨_, (mulV_sound hd hP hu hv).1, (mulV_sound hd hP hu hv).2⟩
  have h0 : ∃ u, vecOK 13 u = true ∧ nv aE 13 u = 1 := ⟨0, by decide, nv_zero aE⟩
  have hpow : ∀ a : CFSG.Sporadic.Fi23.J, (∃ u, vecOK 13 u = true ∧ nv aE 13 u = a) →
      ∀ n : ℕ, ∃ u, vecOK 13 u = true ∧ nv aE 13 u = a ^ n := by
    intro a ha n
    induction n with
    | zero => simpa using h0
    | succ n ih => simpa [pow_succ] using hmul _ _ ih ha
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, hk, rfl⟩ := hg
    exact ⟨4 ^ k, CFSG.KD.Fi23Q.unit_ok k hk, nv_unit aE hk⟩
  | one => exact h0
  | mul a b _ _ ha hb => exact hmul a b ha hb
  | inv a _ ha =>
    obtain ⟨w, hw, he⟩ := hpow a ha (orderOf a - 1)
    refine ⟨w, hw, he.trans ?_⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]

theorem order3_t3
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) {y : CFSG.Sporadic.Fi23.J}
    (hy : y ∈ Subgroup.closure (aE '' Set.Iio 13)) (h3 : y ^ 3 = 1) (h1 : y ≠ 1) :
    ∃ c : Fin 4, IsConj y (t3 c) := by
  obtain ⟨u, hu, rfl⟩ := nf_of_mem aE hH hy
  have hcos : ∀ t < 6561, ∃ D, cosChk CFSG.KD.Fi23Q.H CFSG.KD.Fi23Q.RV 145 (t / 64) D = true :=
    fun t ht => by
      have h : t / 64 < 103 := by omega
      exact CFSG.KD.Fi23Q.cos_all (t / 64) (Nat.zero_le _) h
  have hrep : ∀ ρ < 145, ∃ MV ncl CV WD XD, repChk CFSG.KD.Fi23Q.H CFSG.KD.Fi23Q.RV
      CFSG.KD.Fi23Q.CR 198 ρ MV ncl CV WD XD = true :=
    fun ρ hρ => CFSG.KD.Fi23Q.rep_all ρ (Nat.zero_le _) hρ
  obtain ⟨q, hq, g, -, hg⟩ := order3_conj (eqH_rep aE hH) (elemAb aE hH) (normA aE hH)
    CFSG.KD.Fi23Q.cr_ok hcos hrep hu h3 h1
  obtain ⟨W1, -⟩ := nwR_spec aE (vecOK_dg (CFSG.KD.Fi23Q.cr_ok q hq))
  refine conj_t3_of aE hH hq (w := g) ?_
  change _ = g * wd aE _
  rw [W1, ← hg]
  group

theorem orderOf_three_t3
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) {y : CFSG.Sporadic.Fi23.J}
    (hy : y ∈ Subgroup.closure (aE '' Set.Iio 13)) (h : orderOf y = 3) :
    ∃ c : Fin 4, IsConj y (t3 c) :=
  order3_t3 aE hH hy (by have e := pow_orderOf_eq_one y; rwa [h] at e) fun h1 => by
    rw [h1, orderOf_one] at h
    omega

theorem qG_closure_le :
    Subgroup.closure (qG '' Set.Iio 3) ≤ Subgroup.closure (aE '' Set.Iio 13) := by
  apply Subgroup.closure_mono
  rintro _ ⟨j, hj, rfl⟩
  have hj' : j < 3 := hj
  exact ⟨j, Set.mem_Iio.2 (by omega), aE_lt3 hj'⟩

theorem orderOf_three_Q
    {y : CFSG.Sporadic.Fi23.J} (hy : y ∈ Subgroup.closure (qG '' Set.Iio 3))
    (h : orderOf y = 3) : ∃ c : Fin 4, IsConj y (t3 c) :=
  orderOf_three_t3 aE aE_acts (qG_closure_le hy) h

end CertificateChecks.KernelFi23Q

end
