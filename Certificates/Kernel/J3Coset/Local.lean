module

public import Certificates.Kernel.J3Coset.Core
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowGroup
import Certificates.Kernel.J3Coset.ChecksSmall

public section

namespace CertificateChecks.KernelJ3C

open CFSG.KC.J3C CFSG.KD.J3C CFSG.KS CFSG.KS.Raw.Orb MulAction
  CFSG.AGLEmbedding.KFactProofs.J3Sylow CFSG.Quasithin

theorem rep_zero (w : List ℕ) : rep 0 w = [] := rfl

theorem rep_succ (k : ℕ) (w : List ℕ) : rep (k + 1) w = w ++ rep k w := by
  simp [rep, List.replicate_succ]

theorem rep_codes {w : List ℕ} (hw : ∀ c ∈ w, c < 8) (k : ℕ) : ∀ c ∈ rep k w, c < 8 := by
  induction k with
  | zero => simp [rep_zero]
  | succ k ih =>
    rw [rep_succ]
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact hw c h
    · exact ih c h

theorem pw_codes (w : List Bool) : ∀ c ∈ pw w, c < 8 := by
  intro c hc
  unfold pw at hc
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
  cases b <;> decide

theorem ne_of_nb {a b : ℕ} (h : (!(a == b)) = true) : a ≠ b := by
  simpa using h

theorem eq_of_b {a b : ℕ} (h : (a == b) = true) : a = b := by
  simpa using h

section Local

variable {J : Type} [Group J] [MulAction J (Fin nn)] {g : ℕ → J}

theorem ev_rep (k : ℕ) (w : List ℕ) : ev g (rep k w) = ev g w ^ k := by
  induction k with
  | zero => rw [rep_zero, ev_nil, pow_zero]
  | succ k ih => rw [rep_succ, ev_append, ih, pow_succ']

theorem ev_pw (w : List Bool) : ev g (pw w) = evalW (g 6) (g 7) w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have e : pw (b :: w) = (if b then 7 else 6) :: pw w := rfl
    rw [e, ev_cons, ih]
    cases b <;> simp [evalW]

@[expose] def PP (g : ℕ → J) : Subgroup J := Subgroup.closure ({g 6, g 7} : Set J)

theorem ev_P {w : List ℕ} (hw : codesIn 6 7 w = true) : ev g w ∈ PP g :=
  ev_mem fun c hc => by
    rcases codesIn_mem hw c hc with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem q_facts : (Qr.map Prod.fst).Nodup ∧ Qr.length = 243 ∧ memB (maskOf Qr) beta0 = true ∧
    ∀ r ∈ Qr, codesIn 6 7 r.2 = true ∧ wv tb r.2 beta0 = r.1 ∧
      memB (maskOf Qr) (tb 6 r.1) = true ∧ memB (maskOf Qr) (tb 7 r.1) = true := by
  have h := q_ok
  simp only [qChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  exact ⟨(sortedB_pairwise h1).imp (fun hab => Nat.ne_of_lt hab), h2, h3, h4⟩

theorem mem_Q_iff {x : ℕ} : memB (maskOf Qr) x = true ↔ x ∈ Qr.map Prod.fst := by
  rw [memB_maskOf, List.mem_map]

variable (hg : Acts g)
include hg

theorem P_le_stab : PP g ≤ stabilizer J pt0 := by
  rw [PP, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact fix_letter hg (by decide) fix_facts.2.2.1
  · exact fix_letter hg (by decide) fix_facts.2.2.2.1

theorem Q_lt : ∀ x ∈ Qr.map Prod.fst, x < nn := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  rw [← (q_facts.2.2.2 r hr).2.1]
  exact wv_lt hg (codesIn_lt (q_facts.2.2.2 r hr).1 (by decide) (by decide)) beta0_lt

variable [Finite J]

theorem P_inv {x : J} (hx : x ∈ PP g) :
    ∀ q : Fin nn, q.val ∈ Qr.map Prod.fst → (x • q).val ∈ Qr.map Prod.fst := by
  have hgen : ∀ c, c = 6 ∨ c = 7 → ∀ q : Fin nn, q.val ∈ Qr.map Prod.fst →
      (g c • q).val ∈ Qr.map Prod.fst := by
    intro c hc q hq
    obtain ⟨r, hr, hrq⟩ := List.mem_map.1 hq
    rw [hg c (by omega) q, ← hrq, ← mem_Q_iff]
    rcases hc with rfl | rfl
    · exact (q_facts.2.2.2 r hr).2.2.1
    · exact (q_facts.2.2.2 r hr).2.2.2
  have hpow : ∀ y : J, (∀ q : Fin nn, q.val ∈ Qr.map Prod.fst → (y • q).val ∈ Qr.map Prod.fst) →
      ∀ m : ℕ, ∀ q : Fin nn, q.val ∈ Qr.map Prod.fst → ((y ^ m) • q).val ∈ Qr.map Prod.fst := by
    intro y hy m
    induction m with
    | zero => intro q hq; rwa [pow_zero, one_smul]
    | succ m ih => intro q hq; rw [pow_succ', mul_smul]; exact hy _ (ih q hq)
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact hgen 6 (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hgen 7 (Or.inr rfl)
  | one => intro q hq; rwa [one_smul]
  | mul y z _ _ hy hz => intro q hq; rw [mul_smul]; exact hy _ (hz q hq)
  | inv y _ hy =>
    have h1 : y⁻¹ = y ^ (orderOf y - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos y), pow_orderOf_eq_one]
    rw [h1]
    exact hpow y hy _

theorem elt_of_P (hJ : Nat.card J = 50232960) {x : J} (hx : x ∈ PP g) :
    ∃ r ∈ Qr, x = ev g r.2 ∧ r.1 = (x • ptB).val := by
  have hq : (x • ptB).val ∈ Qr.map Prod.fst :=
    P_inv hg hx ptB (mem_Q_iff.1 q_facts.2.2.1)
  obtain ⟨r, hr, hrq⟩ := List.mem_map.1 hq
  obtain ⟨hc, hv, -⟩ := q_facts.2.2.2 r hr
  refine ⟨r, hr, base_eq hJ hg ?_ ?_, hrq⟩
  · rw [mem_stabilizer_iff.1 (P_le_stab hg hx),
      mem_stabilizer_iff.1 (P_le_stab hg (ev_P hc))]
  · apply Fin.ext
    rw [ev_smul hg (codesIn_lt hc (by decide) (by decide))]
    exact hrq.symm.trans hv.symm

theorem card_P (hJ : Nat.card J = 50232960) : Nat.card (PP g) = 243 := by
  let f : PP g → Fin nn := fun x => x.1 • ptB
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply base_eq hJ hg _ hxy
    rw [mem_stabilizer_iff.1 (P_le_stab hg x.2), mem_stabilizer_iff.1 (P_le_stab hg y.2)]
  have hrange : Set.range f = {q : Fin nn | q.val ∈ Qr.map Prod.fst} := by
    ext q
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, rfl⟩
      exact P_inv hg x.2 ptB (mem_Q_iff.1 q_facts.2.2.1)
    · intro hq
      obtain ⟨r, hr, hrq⟩ := List.mem_map.1 hq
      obtain ⟨hc, hv, -⟩ := q_facts.2.2.2 r hr
      refine ⟨⟨ev g r.2, ev_P hc⟩, Fin.ext ?_⟩
      change (ev g r.2 • ptB).val = q.val
      rw [ev_smul hg (codesIn_lt hc (by decide) (by decide))]
      exact hv.trans hrq
  rw [← Nat.card_range_of_injective hinj, hrange, Nat.card_coe_set_eq,
    ncard_val_mem q_facts.1 (Q_lt hg), List.length_map, q_facts.2.1]

end Local

theorem ld_facts : codesIn 6 7 cw1 = true ∧ codesIn 6 7 cw2 = true ∧
    baseEq tb beta0 ([5, 6] ++ rep 7 [5]) cw1 = true ∧
    baseEq tb beta0 ([5, 7] ++ rep 7 [5]) cw2 = true ∧ baseEq tb beta0 (rep 8 [5]) [] = true ∧
    (!(wv tb (rep 4 [5]) beta0 == beta0)) = true ∧
    (!(wv tb [6, 7] beta0 == wv tb [7, 6] beta0)) = true ∧
    sortedB (Zr.map Prod.fst) = true ∧ (Zr.length == 9) = true ∧
    (∀ r ∈ Zr, (codesIn 6 7 r.2 && wv tb r.2 beta0 == r.1 &&
      baseEq tb beta0 (r.2 ++ [6]) ([6] ++ r.2) && baseEq tb beta0 (r.2 ++ [7]) ([7] ++ r.2) &&
      baseEq tb beta0 (rep 3 r.2) [] &&
      (r.1 == beta0 || (!(wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 == beta0) &&
        !(wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 == r.1) &&
        !(wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 == wv tb (r.2 ++ r.2) beta0)))) = true) ∧
    (∀ r ∈ Qr, (memB (maskOf Zr) r.1 || !(wv tb (r.2 ++ [6]) beta0 == wv tb ([6] ++ r.2) beta0) ||
      !(wv tb (r.2 ++ [7]) beta0 == wv tb ([7] ++ r.2) beta0)) = true) ∧
    (zc.length == 9) = true ∧
    (∀ r ∈ Zr.zip zc, baseEq tb beta0 ([5] ++ r.1.2 ++ rep 7 [5]) (Zr.getD r.2 (0, [])).2 = true) ∧
    (zk.length == 7) = true ∧
    (∀ r ∈ (List.range' 1 7).zip zk, (!(wv tb (rep r.1 [5] ++ (Zr.getD r.2 (0, [])).2) beta0 ==
      wv tb ((Zr.getD r.2 (0, [])).2 ++ rep r.1 [5]) beta0)) = true) ∧
    baseEq tb beta0 ([5, 5, 6] ++ rep 6 [5]) (pw sw1) = true ∧
    baseEq tb beta0 ([5, 5, 7] ++ rep 6 [5]) (pw sw2) = true := by
  have h := ld_ok
  unfold ldChk at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, List.all_eq_true.1 h10, List.all_eq_true.1 h11,
    h12, List.all_eq_true.1 h13, h14, List.all_eq_true.1 h15, h16, h17⟩

theorem idx_facts : (∀ i ∈ zc, i < 9) ∧ (∀ i ∈ zk, i < 9) := by
  have h := idx_ok
  simp only [idxChk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem Zr_len : Zr.length = 9 := eq_of_b ld_facts.2.2.2.2.2.2.2.2.1

theorem zr_lt (i : Fin 9) : i.val < Zr.length := by
  rw [Zr_len]
  exact i.isLt

theorem s_codes : ∀ c ∈ [5], c < 8 := by decide

theorem codes_app {u v : List ℕ} (hu : ∀ c ∈ u, c < 8) (hv : ∀ c ∈ v, c < 8) :
    ∀ c ∈ u ++ v, c < 8 := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact hu c h
  · exact hv c h

theorem conj_codes {w : List ℕ} (hw : ∀ c ∈ w, c < 8) : ∀ c ∈ [5] ++ w ++ rep 7 [5], c < 8 :=
  codes_app (codes_app s_codes hw) (rep_codes s_codes 7)

theorem zr_nodup : (Zr.map Prod.fst).Nodup :=
  (sortedB_pairwise ld_facts.2.2.2.2.2.2.2.1).imp (fun hab => Nat.ne_of_lt hab)

section LocalData

variable {J : Type} [Group J] [Finite J] [MulAction J (Fin nn)] {g : ℕ → J}

@[expose] noncomputable def zz (g : ℕ → J) (i : Fin 9) : J := ev g (Zr.getD i.val (0, [])).2

theorem zr_get (i : Fin 9) : Zr.getD i.val (0, []) = Zr[i.val]'(zr_lt i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (zr_lt i), Option.getD_some]

theorem zr_facts (r : ℕ × List ℕ) (hr : r ∈ Zr) : codesIn 6 7 r.2 = true ∧
    wv tb r.2 beta0 = r.1 ∧ baseEq tb beta0 (r.2 ++ [6]) ([6] ++ r.2) = true ∧
    baseEq tb beta0 (r.2 ++ [7]) ([7] ++ r.2) = true ∧ baseEq tb beta0 (rep 3 r.2) [] = true ∧
    (r.1 = beta0 ∨ (wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 ≠ beta0 ∧
      wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 ≠ r.1 ∧
      wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 ≠ wv tb (r.2 ++ r.2) beta0)) := by
  have h := ld_facts.2.2.2.2.2.2.2.2.2.1 r hr
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem ev_pair (a b : ℕ) : ev g [a, b] = g a * g b := by simp [ev]

variable (hg : Acts g)
include hg

theorem s_pow8 (hJ : Nat.card J = 50232960) : g 5 ^ 8 = 1 := by
  have h := word_eq hJ hg (rep 8 [5]) [] (rep_codes s_codes 8) (by decide) ld_facts.2.2.2.2.1
  rwa [ev_rep, ev_single, ev_nil] at h

theorem s_inv (hJ : Nat.card J = 50232960) : (g 5)⁻¹ = g 5 ^ 7 := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ, s_pow8 hg hJ]

theorem conj_word (hJ : Nat.card J = 50232960) (w : List ℕ) :
    ev g ([5] ++ w ++ rep 7 [5]) = g 5 * ev g w * (g 5)⁻¹ := by
  rw [ev_append, ev_append, ev_single, ev_rep, ev_single, s_inv hg hJ]

theorem zz_facts (hJ : Nat.card J = 50232960) (i : Fin 9) :
    zz g i ∈ PP g ∧ zz g i * g 6 = g 6 * zz g i ∧ zz g i * g 7 = g 7 * zz g i ∧
      zz g i ^ 3 = 1 ∧ (zz g i • ptB).val = (Zr[i.val]'(zr_lt i)).1 := by
  have hr := List.getElem_mem (l := Zr) (zr_lt i)
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := zr_facts _ hr
  have hc := codesIn_lt h1 (by decide) (by decide)
  unfold zz
  rw [zr_get]
  refine ⟨ev_P h1, ?_, ?_, ?_, ?_⟩
  · have := word_eq hJ hg _ _ (codes_app hc (by decide)) (codes_app (by decide) hc) h3
    rwa [ev_append, ev_append, ev_single] at this
  · have := word_eq hJ hg _ _ (codes_app hc (by decide)) (codes_app (by decide) hc) h4
    rwa [ev_append, ev_append, ev_single] at this
  · have := word_eq hJ hg _ [] (rep_codes hc 3) (by decide) h5
    rwa [ev_rep, ev_nil] at this
  · rw [ev_smul hg hc]
    exact h2

theorem localData (hJ : Nat.card J = 50232960) :
    LocalData (stabilizer J pt0) (g 6) (g 7) (g 5) (zz g) sw1 sw2 where
  t₁_mem := fix_letter hg (by decide) fix_facts.2.2.1
  t₂_mem := fix_letter hg (by decide) fix_facts.2.2.2.1
  s_mem := fix_letter hg (by decide) fix_facts.2.1
  card_H := card_stab hJ hg
  card_P := card_P hg hJ
  conj₁ := by
    have h := word_eq hJ hg ([5, 6] ++ rep 7 [5]) cw1 (conj_codes (w := [6]) (by decide))
      (codesIn_lt ld_facts.1 (by decide) (by decide)) ld_facts.2.2.1
    have e : ev g ([5, 6] ++ rep 7 [5]) = g 5 * g 6 * (g 5)⁻¹ := by
      rw [show ([5, 6] ++ rep 7 [5] : List ℕ) = [5] ++ [6] ++ rep 7 [5] from rfl,
        conj_word hg hJ, ev_single]
    rw [← e, h]
    exact ev_P ld_facts.1
  conj₂ := by
    have h := word_eq hJ hg ([5, 7] ++ rep 7 [5]) cw2 (conj_codes (w := [7]) (by decide))
      (codesIn_lt ld_facts.2.1 (by decide) (by decide)) ld_facts.2.2.2.1
    have e : ev g ([5, 7] ++ rep 7 [5]) = g 5 * g 7 * (g 5)⁻¹ := by
      rw [show ([5, 7] ++ rep 7 [5] : List ℕ) = [5] ++ [7] ++ rep 7 [5] from rfl,
        conj_word hg hJ, ev_single]
    rw [← e, h]
    exact ev_P ld_facts.2.1
  s_pow_eight := s_pow8 hg hJ
  s_pow_four := by
    intro h
    have hne := word_ne hg (rep 4 [5]) [] (rep_codes s_codes 4) (by decide) beta0_lt
      (ne_of_nb ld_facts.2.2.2.2.2.1)
    apply hne
    rw [ev_rep, ev_single, h, ev_nil]
  noncomm := by
    intro h
    have hne := word_ne hg [6, 7] [7, 6] (by decide) (by decide) beta0_lt
      (ne_of_nb ld_facts.2.2.2.2.2.2.1)
    apply hne
    rw [ev_pair, ev_pair]
    exact h
  Z_mem := by
    intro x
    constructor
    · intro hx
      obtain ⟨hxP, hxc⟩ := mem_centerOf.1 hx
      obtain ⟨r, hr, rfl, hrq⟩ := elt_of_P hg hJ hxP
      obtain ⟨hc, hv, -⟩ := q_facts.2.2.2 r hr
      have hc8 := codesIn_lt hc (by decide) (by decide)
      have h11 := ld_facts.2.2.2.2.2.2.2.2.2.2.1 r hr
      simp only [Bool.or_eq_true] at h11
      rcases h11 with (h | h) | h
      · obtain ⟨z, hz, hzr⟩ := (memB_maskOf Zr r.1).1 h
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
        have hi9 : i < 9 := Zr_len ▸ hi
        refine ⟨⟨i, hi9⟩, ?_⟩
        obtain ⟨hzP, -, -, -, hzv⟩ := zz_facts hg hJ ⟨i, hi9⟩
        apply base_eq hJ hg
        · rw [mem_stabilizer_iff.1 (P_le_stab hg (ev_P hc)),
            mem_stabilizer_iff.1 (P_le_stab hg hzP)]
        · apply Fin.ext
          rw [hzv, ← hrq]
          exact hzr.symm
      · exfalso
        have hne := word_ne hg (r.2 ++ [6]) ([6] ++ r.2) (codes_app hc8 (by decide))
          (codes_app (by decide) hc8) beta0_lt (ne_of_nb h)
        apply hne
        rw [ev_append, ev_append, ev_single]
        exact (hxc (g 6) (Subgroup.subset_closure (by simp))).symm
      · exfalso
        have hne := word_ne hg (r.2 ++ [7]) ([7] ++ r.2) (codes_app hc8 (by decide))
          (codes_app (by decide) hc8) beta0_lt (ne_of_nb h)
        apply hne
        rw [ev_append, ev_append, ev_single]
        exact (hxc (g 7) (Subgroup.subset_closure (by simp))).symm
    · rintro ⟨i, rfl⟩
      obtain ⟨hP, h6, h7, -, -⟩ := zz_facts hg hJ i
      rw [mem_centerOf]
      refine ⟨hP, fun y hy => ?_⟩
      have hle : PP g ≤ Subgroup.centralizer {zz g i} := by
        rw [PP, Subgroup.closure_le]
        rintro _ (rfl | h)
        · exact Subgroup.mem_centralizer_singleton_iff.2 h6.symm
        · rw [Set.mem_singleton_iff] at h
          subst h
          exact Subgroup.mem_centralizer_singleton_iff.2 h7.symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  Z_inj := by
    intro i j hij
    have h1 := (zz_facts hg hJ i).2.2.2.2
    have h2 := (zz_facts hg hJ j).2.2.2.2
    rw [hij, h2] at h1
    apply Fin.ext
    have e1 : (Zr.map Prod.fst)[i.val]'(by rw [List.length_map]; exact zr_lt i) =
        (Zr.map Prod.fst)[j.val]'(by rw [List.length_map]; exact zr_lt j) := by
      rw [List.getElem_map, List.getElem_map]
      exact h1.symm
    exact (List.Nodup.getElem_inj_iff zr_nodup).1 e1
  Z_cube := fun i => (zz_facts hg hJ i).2.2.2.1
  Z_conj := by
    intro i
    have hzc : zc.length = 9 := eq_of_b ld_facts.2.2.2.2.2.2.2.2.2.2.2.1
    have hiz : i.val < zc.length := by rw [hzc]; exact i.isLt
    have hj : zc[i.val] < 9 := idx_facts.1 _ (List.getElem_mem hiz)
    refine ⟨⟨zc[i.val], hj⟩, ?_⟩
    have hmem : (Zr[i.val]'(zr_lt i), zc[i.val]) ∈ Zr.zip zc := by
      rw [List.mem_iff_getElem]
      refine ⟨i.val, by rw [List.length_zip, Zr_len, hzc, Nat.min_self]; exact i.isLt, ?_⟩
      rw [List.getElem_zip]
    have h := ld_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hmem
    have hr := List.getElem_mem (l := Zr) (zr_lt i)
    have hc8 := codesIn_lt (zr_facts _ hr).1 (by decide) (by decide)
    have hj' := List.getElem_mem (l := Zr) (zr_lt ⟨zc[i.val], hj⟩)
    have hc8' := codesIn_lt (zr_facts _ hj').1 (by decide) (by decide)
    have hget : Zr.getD zc[i.val] (0, []) = Zr[zc[i.val]]'(zr_lt ⟨zc[i.val], hj⟩) :=
      zr_get ⟨zc[i.val], hj⟩
    rw [hget] at h
    have e := word_eq hJ hg _ _ (conj_codes hc8) hc8' h
    rw [conj_word hg hJ] at e
    unfold zz
    rw [zr_get i, hget]
    exact e
  Z_irred := by
    intro i hne
    have hr := List.getElem_mem (l := Zr) (zr_lt i)
    obtain ⟨hc, hv, -, -, -, h6⟩ := zr_facts _ hr
    have hc8 := codesIn_lt hc (by decide) (by decide)
    obtain ⟨hP, -, -, -, hzv⟩ := zz_facts hg hJ i
    rcases h6 with h | ⟨h1, h2, h3⟩
    · exfalso
      apply hne
      apply free hJ hg (P_le_stab hg hP)
      apply Fin.ext
      rw [hzv, h]
      rfl
    · have hcw := conj_codes hc8
      have hzi : zz g i = ev g (Zr[i.val]'(zr_lt i)).2 := by unfold zz; rw [zr_get]
      have e := conj_word hg hJ (g := g) (Zr[i.val]'(zr_lt i)).2
      rw [← hzi] at e
      refine ⟨?_, ?_, ?_⟩
      · rw [← e]
        exact word_ne hg _ [] hcw (by decide) beta0_lt h1
      · rw [← e, hzi]
        exact word_ne hg _ _ hcw hc8 beta0_lt (by rw [hv]; exact h2)
      · rw [← e, hzi, sq, ← ev_append]
        exact word_ne hg _ _ hcw (codes_app hc8 hc8) beta0_lt h3
  Z_cent := by
    intro k hk0 hk8
    have hzk : zk.length = 7 := eq_of_b ld_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hkz : k - 1 < zk.length := by rw [hzk]; omega
    have hj : zk[k - 1] < 9 := idx_facts.2 _ (List.getElem_mem hkz)
    refine ⟨⟨zk[k - 1], hj⟩, ?_⟩
    have hmem : (k, zk[k - 1]) ∈ (List.range' 1 7).zip zk := by
      rw [List.mem_iff_getElem]
      refine ⟨k - 1, by rw [List.length_zip, List.length_range', hzk, Nat.min_self]; omega, ?_⟩
      rw [List.getElem_zip, List.getElem_range']
      congr 1
      omega
    have h := ld_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hmem
    have hj' := List.getElem_mem (l := Zr) (zr_lt ⟨zk[k - 1], hj⟩)
    have hc8 := codesIn_lt (zr_facts _ hj').1 (by decide) (by decide)
    have hzi : zz g ⟨zk[k - 1], hj⟩ = ev g (Zr.getD zk[k - 1] (0, [])).2 := rfl
    rw [zr_get ⟨zk[k - 1], hj⟩] at h hzi
    have hne := word_ne hg _ _ (codes_app (rep_codes s_codes k) hc8)
      (codes_app hc8 (rep_codes s_codes k)) beta0_lt (ne_of_nb h)
    rw [ev_append, ev_append, ev_rep, ev_single] at hne
    rw [hzi]
    exact hne
  w₁_eq := by
    have h := word_eq hJ hg ([5, 5, 6] ++ rep 6 [5]) (pw sw1)
      (codes_app (by decide) (rep_codes s_codes 6)) (pw_codes sw1)
      ld_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [ev_pw] at h
    have hs6 : (g 5 ^ 2)⁻¹ = g 5 ^ 6 :=
      (eq_inv_of_mul_eq_one_right (by rw [← pow_add, s_pow8 hg hJ])).symm
    rw [← h, hs6, ev_append, ev_rep, ev_single]
    simp [ev, pow_two, mul_assoc]
  w₂_eq := by
    have h := word_eq hJ hg ([5, 5, 7] ++ rep 6 [5]) (pw sw2)
      (codes_app (by decide) (rep_codes s_codes 6)) (pw_codes sw2)
      ld_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [ev_pw] at h
    have hs6 : (g 5 ^ 2)⁻¹ = g 5 ^ 6 :=
      (eq_inv_of_mul_eq_one_right (by rw [← pow_add, s_pow8 hg hJ])).symm
    rw [← h, hs6, ev_append, ev_rep, ev_single]
    simp [ev, pow_two, mul_assoc]
  sing := by decide +kernel

end LocalData

end CertificateChecks.KernelJ3C

end
