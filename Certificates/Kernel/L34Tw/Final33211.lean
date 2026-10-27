module

public import Certificates.Kernel.L34Tw.Final
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwConcXK
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Tw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KC.L34KSnd CFSG.KC.L34Scan CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Tw
open CertificateChecks.KernelLC.L34Cert CertificateChecks.KernelLC.L34Para
open CFSG.KC.L34Tw CertificateChecks.KernelLC.L34TwD
open CFSG.KLie.CT (andB orB notB)

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem orB_nt (b : Bool) : orB (notB true) b = b := rfl

theorem cntN_succ (n : Nat) (f : Nat → Bool) :
    cntN (n + 1) f = (if f n = true then 1 else 0) + cntN n f := by
  change Bool.rec (motive := fun _ => Nat) (cntN n f) (Nat.succ (cntN n f)) (f n) = _
  cases f n <;> simp <;> omega

theorem cntN_eq (n : Nat) (f : Nat → Bool) :
    cntN n f = ((Finset.range n).filter fun q => f q = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cntN_succ, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · omega

theorem cntN_le (n : Nat) (f : Nat → Bool) : cntN n f ≤ n := by
  rw [cntN_eq]
  exact (Finset.card_filter_le _ _).trans (Finset.card_range n).le

theorem sumN_succ (n : Nat) (f : Nat → Nat) : sumN (n + 1) f = f n + sumN n f := rfl

theorem tally_eq (a b c : Bool) : tally a b c = (if a = true then 1 else 0) +
    256 * (if (a && b) = true then 1 else 0) + 65536 * (if (a && !c) = true then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem sumN_tally (n : Nat) (a b c : Nat → Bool) :
    sumN n (fun q => tally (a q) (b q) (c q)) =
      cntN n a + 256 * cntN n (fun q => a q && b q) + 65536 * cntN n (fun q => a q && !c q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumN_succ, ih, cntN_succ, cntN_succ, cntN_succ (f := fun q => a q && !c q), tally_eq]
    cases a n <;> cases b n <;> cases c n <;> simp <;> omega

theorem dec3 {n m k : Nat} (hn : n ≤ 64) (hm : m ≤ 64) :
    Nat.land (n + 256 * m + 65536 * k) 255 = n ∧
      Nat.land (Nat.shiftRight (n + 256 * m + 65536 * k) 8) 255 = m ∧
      Nat.shiftRight (n + 256 * m + 65536 * k) 16 = k := by
  have e255 : (255 : Nat) = 2 ^ 8 - 1 := rfl
  have l1 : Nat.land (n + 256 * m + 65536 * k) 255 = n := by
    change (n + 256 * m + 65536 * k) &&& 255 = n
    rw [e255, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have l2 : Nat.land (Nat.shiftRight (n + 256 * m + 65536 * k) 8) 255 = m := by
    change (n + 256 * m + 65536 * k) >>> 8 &&& 255 = m
    rw [e255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    omega
  have l3 : Nat.shiftRight (n + 256 * m + 65536 * k) 16 = k := by
    change (n + 256 * m + 65536 * k) >>> 16 = k
    rw [Nat.shiftRight_eq_div_pow]
    omega
  exact ⟨l1, l2, l3⟩

theorem tallyOK_spec {s Q J : Nat} (h : tallyOK s Q J = true) :
    Nat.land s 255 ≤ Q ∧ Nat.land (Nat.shiftRight s 8) 255 ≤ J ∧ Nat.shiftRight s 16 = 0 := by
  unfold tallyOK at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

noncomputable def el (q : Nat) : Equiv.Perm (Fin 42) :=
  if h : q < 64 then (rpT h).choose else 1

theorem el_spec {q : Nat} (hq : q < 64) : el q ∈ T0 ∧ Rp (L34PT.T q) (el q) := by
  unfold el
  rw [dif_pos hq]
  exact (rpT hq).choose_spec

theorem toList_get {i : Nat} (hi : i < 64) :
    (pts 42 6 64 L34PT.T).toList[i]'(by rw [Array.length_toList, size_pts]; exact hi) =
      unpack 42 6 (L34PT.T i) := by
  rw [Array.getElem_toList, ← getElem!_pos (pts 42 6 64 L34PT.T) i (by rw [size_pts]; exact hi),
    pts_get' hi]

theorem el_inj {q q' : Nat} (hq : q < 64) (hq' : q' < 64) (e : el q = el q') : q = q' := by
  have h1 := (el_spec hq).2.2
  have h2 := (el_spec hq').2.2
  rw [e] at h1
  have := h1.tab_eq h2
  rw [← toList_get hq, ← toList_get hq'] at this
  exact (List.Nodup.getElem_inj_iff enumT.nodup).1 this

theorem el_of_mem {g : Equiv.Perm (Fin 42)} (hg : g ∈ T0) : ∃ q < 64, el q = g := by
  obtain ⟨q, hq, hr⟩ := rpT' hg
  exact ⟨q, hq, (el_spec hq).2.2.perm_eq hr.2⟩

noncomputable def elc (i : Bool) (q : Nat) : Equiv.Perm (Fin 42) := if i then el q * r₄ else el q

theorem rp₄ : Rp r₄K r₄ := rp₅.mul rp₆

theorem elc_spec (i : Bool) {q : Nat} (hq : q < 64) :
    elc i q ∈ cosT i ∧ Rp (cosK L34PT.T r₄K (if i then 1 else 0) q) (elc i q) := by
  cases i
  · exact ⟨(el_spec hq).1, (el_spec hq).2⟩
  · exact ⟨⟨el q, (el_spec hq).1, rfl⟩, (el_spec hq).2.mul rp₄⟩

theorem elc_inj (i : Bool) {q q' : Nat} (hq : q < 64) (hq' : q' < 64) (e : elc i q = elc i q') :
    q = q' := by
  cases i
  · exact el_inj hq hq' e
  · exact el_inj hq hq' (mul_right_cancel e)

theorem elc_of_mem {i : Bool} {g : Equiv.Perm (Fin 42)} (hg : g ∈ cosT i) :
    ∃ q < 64, elc i q = g := by
  cases i
  · exact el_of_mem hg
  · obtain ⟨x, hx, rfl⟩ := hg
    obtain ⟨q, hq, rfl⟩ := el_of_mem hx
    exact ⟨q, hq, rfl⟩

theorem card_cos (i : Bool) {X : Set (Equiv.Perm (Fin 42))} {P : Equiv.Perm (Fin 42) → Prop}
    (hX : ∀ y, y ∈ X ↔ y ∈ cosT i ∧ P y) {f : Nat → Bool}
    (hf : ∀ q < 64, f q = true ↔ P (elc i q)) : Nat.card X = cntN 64 f := by
  classical
  have hXe : X = ↑(((Finset.range 64).filter fun q => f q = true).image (elc i)) := by
    ext y
    rw [hX, Finset.coe_image]
    constructor
    · rintro ⟨hy, hP⟩
      obtain ⟨q, hq, rfl⟩ := elc_of_mem hy
      exact ⟨q, by simp [hq, (hf q hq).2 hP], rfl⟩
    · rintro ⟨q, hq, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hq
      exact ⟨(elc_spec i hq.1).1, (hf q hq.1).1 hq.2⟩
  rw [hXe, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn, cntN_eq]
  intro q hq q' hq' e
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hq hq'
  exact elc_inj i hq.1 hq'.1 e

theorem tallyC_eval (i : Bool) {t u : Equiv.Perm (Fin 42)} {tk uk : Nat} (ht : Rp tk t)
    (hu : Rp uk u) {ok : Nat → Bool} {O : Equiv.Perm (Fin 42) → Prop}
    (hok : ∀ {x : Nat} {g : Equiv.Perm (Fin 42)}, Rp x g → (ok x = true ↔ O g)) :
    ∃ k, sumN 64 (tallyC L34PT.T r₄K tk uk (if i then 1 else 0) ok) =
      Nat.card (cosC i t u) + 256 * Nat.card (cosC₂ i t u) + 65536 * k ∧
      Nat.card (cosC i t u) ≤ 64 ∧ Nat.card (cosC₂ i t u) ≤ 64 ∧
      (k = 0 → ∀ y ∈ cosC i t u, O (y * y)) := by
  have he : tallyC L34PT.T r₄K tk uk (if i then 1 else 0) ok = fun q =>
      tally (andB (commK (cosK L34PT.T r₄K (if i then 1 else 0) q) tk)
          (commK (cosK L34PT.T r₄K (if i then 1 else 0) q) uk))
        (Nat.beq (mulK (cosK L34PT.T r₄K (if i then 1 else 0) q)
          (cosK L34PT.T r₄K (if i then 1 else 0) q)) idK)
        (ok (mulK (cosK L34PT.T r₄K (if i then 1 else 0) q)
          (cosK L34PT.T r₄K (if i then 1 else 0) q))) := by
    funext q
    unfold tallyC
    rw [sN]
    cases andB (commK (cosK L34PT.T r₄K (if i then 1 else 0) q) tk)
      (commK (cosK L34PT.T r₄K (if i then 1 else 0) q) uk)
    · rfl
    · change strictN _ _ = _
      rw [sN]
  rw [he, sumN_tally]
  have hin : ∀ q < 64, andB (commK (cosK L34PT.T r₄K (if i then 1 else 0) q) tk)
      (commK (cosK L34PT.T r₄K (if i then 1 else 0) q) uk) = true ↔
        elc i q * t = t * elc i q ∧ elc i q * u = u * elc i q := fun q hq => by
    have hy := (elc_spec i hq).2
    rw [andB_iff, hy.comm ht, hy.comm hu]
  have e1 := card_cos i (X := cosC i t u) (P := fun y => y * t = t * y ∧ y * u = u * y)
      (fun y => Iff.rfl) hin
  have e2 := card_cos i (X := cosC₂ i t u)
      (P := fun y => (y * t = t * y ∧ y * u = u * y) ∧ y * y = 1)
      (fun y => by simp only [cosC₂, cosC, Set.mem_setOf_eq, and_assoc]) (fun q hq => by
        have hy := (elc_spec i hq).2
        rw [Bool.and_eq_true]
        exact and_congr (hin q hq) ((hy.mul hy).beq_iff rp_id))
  refine ⟨_, by rw [e1, e2], e1 ▸ cntN_le _ _, e2 ▸ cntN_le _ _, fun h3 => ?_⟩
  · rintro y ⟨hy, hyt, hyu⟩
    obtain ⟨q, hq, rfl⟩ := elc_of_mem hy
    have hr := (elc_spec i hq).2
    by_contra hO
    have hz : cntN 64 (fun q => andB (commK (cosK L34PT.T r₄K (if i then 1 else 0) q) tk)
        (commK (cosK L34PT.T r₄K (if i then 1 else 0) q) uk) &&
          !ok (mulK (cosK L34PT.T r₄K (if i then 1 else 0) q)
            (cosK L34PT.T r₄K (if i then 1 else 0) q))) ≠ 0 := by
      rw [cntN_eq]
      refine Finset.card_ne_zero.2 ⟨q, ?_⟩
      rw [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, (hin q hq).2 ⟨hyt, hyu⟩,
        Bool.not_eq_true', ← Bool.not_eq_true, hok (hr.mul hr)]
      exact ⟨hq, rfl, hO⟩
    exact hz h3

theorem tallyC_sum (i : Bool) {t u : Equiv.Perm (Fin 42)} {tk uk : Nat} (ht : Rp tk t)
    (hu : Rp uk u) {ok : Nat → Bool} {O : Equiv.Perm (Fin 42) → Prop}
    (hok : ∀ {x : Nat} {g : Equiv.Perm (Fin 42)}, Rp x g → (ok x = true ↔ O g))
    {Q J : Nat} (h : tallyOK (sumN 64 (tallyC L34PT.T r₄K tk uk (if i then 1 else 0) ok)) Q J = true) :
    Nat.card (cosC i t u) ≤ Q ∧ Nat.card (cosC₂ i t u) ≤ J ∧
      ∀ y ∈ cosC i t u, O (y * y) := by
  obtain ⟨k, e, h1, h2, hk⟩ := tallyC_eval i ht hu hok
  obtain ⟨l1, l2, l3⟩ := dec3 (k := k) h1 h2
  obtain ⟨c1, c2, c3⟩ := tallyOK_spec h
  rw [e, l1, l2, l3] at *
  exact ⟨c1, c2, hk c3⟩

theorem data_vals : Q 0 = 8 ∧ Q 1 = 8 ∧ I 0 = 2 ∧ I 1 = 2 := by decide

theorem rpT_of {x : Equiv.Perm (Fin 42)} (hx : x ∈ cosT true) :
    ∃ c < 64, Rp (mulK (L34PT.T c) r₄K) x := by
  obtain ⟨q, hq, rfl⟩ := elc_of_mem hx
  exact ⟨q, hq, (elc_spec true hq).2⟩

theorem q_facts {v : Equiv.Perm (Fin 42)} (hv : v ∈ cosT true) (hvv : v * v = 1) (i : Bool) :
    Nat.card (cosC i v v) ≤ 8 ∧ Nat.card (cosC₂ i v v) ≤ 2 ∧
      ∀ y ∈ cosC i v v, y * y * (y * y) = 1 := by
  obtain ⟨c, hc, hr⟩ := rpT_of hv
  have h0 := ch33211_q
  unfold qAllK at h0
  have h := allN' h0 c hc
  rw [sB] at h
  rw [orB_iff, notB_iff, hr.inv2.2 hvv] at h
  have hq := allN' (h.resolve_left (by decide)) (if i then 1 else 0) (by cases i <;> decide)
  obtain ⟨q0, q1, i0, i1⟩ := data_vals
  have hQ : Q (if i then 1 else 0) = 8 := by cases i <;> assumption
  have hI : I (if i then 1 else 0) = 2 := by cases i <;> assumption
  rw [hQ, hI] at hq
  exact tallyC_sum i hr hr (fun hx => hx.inv2) hq

theorem p_facts {t u : Equiv.Perm (Fin 42)} (ht : t ∈ T0) (htt : t * t = 1) (ht1 : t ≠ 1)
    (hu : u ∈ cosT true) (huu : u * u = 1) (htu : t * u = u * t) :
    Nat.card (cosC false t u) * 8 + Nat.card (cosC true t u) * 8 ≤ 128 ∧
      Nat.card (cosC₂ false t u) * 2 + Nat.card (cosC₂ true t u) * 2 < 16 ∧
      ∀ i, ∀ y ∈ cosC i t u, y * y = 1 ∨ y * y = t := by
  obtain ⟨b, hb, hru⟩ := rpT_of hu
  obtain ⟨a, ha, rfl⟩ := el_of_mem ht
  have hrt := (el_spec ha).2
  have h0 := ch33211_p
  unfold pAllK at h0
  have h := allN' h0 b hb
  rw [sB] at h
  rw [orB_iff, notB_iff, hru.inv2.2 huu] at h
  have h' := allN' (h.resolve_left (by decide)) a ha
  rw [sB] at h'
  have hne : Nat.beq (L34PT.T a) CFSG.KC.L34Tw.idK = false := by
    cases e : Nat.beq (L34PT.T a) CFSG.KC.L34Tw.idK
    · rfl
    · exact absurd ((hrt.beq_iff rp_id).1 e) ht1
  have hcond : andB (inv2K (L34PT.T a)) (andB (notB (Nat.beq (L34PT.T a) CFSG.KC.L34Tw.idK))
      (CFSG.KC.L34Tw.commK (L34PT.T a) (mulK (L34PT.T b) r₄K))) = true := by
    rw [andB_iff, andB_iff, hrt.inv2.2 htt, (hrt.comm hru).2 htu, hne]
    exact ⟨rfl, rfl, rfl⟩
  rw [hcond, orB_nt] at h'
  have hp := h'
  unfold pK at hp
  rw [sB, sB] at hp
  obtain ⟨hs0, hp⟩ := andB_iff.1 hp
  obtain ⟨hs1, hp⟩ := andB_iff.1 hp
  obtain ⟨hc, hi⟩ := andB_iff.1 hp
  have hok : ∀ {x : Nat} {g : Equiv.Perm (Fin 42)}, Rp x g →
      (orB (Nat.beq x idK) (Nat.beq x (L34PT.T a)) = true ↔ g = 1 ∨ g = el a) :=
    fun hx => by rw [orB_iff, hx.beq_iff rp_id, hx.beq_iff hrt]
  obtain ⟨-, -, o0⟩ := tallyC_sum false hrt hru hok hs0
  obtain ⟨-, -, o1⟩ := tallyC_sum true hrt hru hok hs1
  obtain ⟨k0, e0, a0, b0, -⟩ := tallyC_eval false hrt hru hok
  obtain ⟨k1, e1, a1, b1, -⟩ := tallyC_eval true hrt hru hok
  have ep : ∀ i : Bool, pSum L34PT.T r₄K (L34PT.T a) (mulK (L34PT.T b) r₄K) (if i then 1 else 0) =
      sumN 64 (tallyC L34PT.T r₄K (L34PT.T a) (mulK (L34PT.T b) r₄K) (if i then 1 else 0)
        fun A => orB (Nat.beq A idK) (Nat.beq A (L34PT.T a))) := fun _ => rfl
  have ep0 := ep false
  have ep1 := ep true
  simp only [Bool.false_eq_true, ↓reduceIte] at ep0 ep1 e0 e1
  rw [ep0, e0, ep1, e1] at hc hi
  obtain ⟨l1, l2, -⟩ := dec3 (k := k0) a0 b0
  obtain ⟨m1, m2, -⟩ := dec3 (k := k1) a1 b1
  rw [l1, m1, data_vals.1, data_vals.2.1] at hc
  rw [l2, m2, data_vals.2.2.1, data_vals.2.2.2] at hi
  refine ⟨Nat.le_of_ble_eq_true hc, Nat.le_of_ble_eq_true hi, fun i y hy => ?_⟩
  cases i
  · exact o0 y hy
  · exact o1 y hy

theorem cent_fact : ∃ z ∈ T0, z * z = 1 ∧ z ≠ 1 ∧ z * g₅ = g₅ * z ∧ z * g₆ = g₆ * z ∧
    ∀ x ∈ T0, z * x = x * z := by
  have hq := ch33211_idx.1
  obtain ⟨hz, hr⟩ := el_spec hq
  have h := ch33211_cent
  unfold CFSG.KC.L34Tw.centK at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h5⟩ := andB_iff.1 h
  refine ⟨el (D 1), hz, hr.inv2.1 h1, fun e => ?_, (hr.comm rp₅).1 h3, (hr.comm rp₆).1 h4, ?_⟩
  · rw [notB_iff, (hr.beq_iff rp_id).2 e] at h2
    exact absurd h2 (by decide)
  · have hle : T0 ≤ Subgroup.centralizer {el (D 1)} := by
      unfold T0
      rw [Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      have hi4 : i < 4 := hi
      have := (hr.comm (rpG hi4)).1 (allN' h5 i hi4)
      rw [List.getD_eq_getElem _ _ hi] at this
      exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem inv_fact : ∃ x ∈ T0, x * r₄ * (x * r₄) = 1 := by
  obtain ⟨hx, hr⟩ := el_spec ch33211_idx.2
  exact ⟨_, hx, (hr.mul rp₄).inv2.1 ch33211_inv⟩

theorem uni_fact : ∀ x ∈ T0, x * r₄ * (x * r₄) = 1 → ∃ c ∈ T0, x * r₄ * c = c * r₄ := by
  intro x hx hxx
  obtain ⟨q, hq, rfl⟩ := el_of_mem hx
  have hr := (el_spec hq).2.mul rp₄
  have h0 := ch33211_uni
  unfold uniK at h0
  have h := allN' h0 q hq
  rw [sB, orB_iff, notB_iff, hr.inv2.2 hxx] at h
  obtain ⟨hU, h⟩ := andB_iff.1 (h.resolve_left (by decide))
  rw [sB] at h
  obtain ⟨hc, rc⟩ := el_spec (Nat.le_of_ble_eq_true hU)
  exact ⟨_, hc, ((hr.mul rc).beq_iff (rc.mul rp₄)).1 h⟩

theorem big_fact : ∀ t ∈ T0, t * t = 1 → 16 ≤ Nat.card (cosC false t t) := by
  intro t ht htt
  obtain ⟨a, ha, rfl⟩ := el_of_mem ht
  have hrt := (el_spec ha).2
  have h0 := ch33211_big
  unfold bigK at h0
  have h := allN' h0 a ha
  rw [sB, orB_iff, notB_iff, hrt.inv2.2 htt] at h
  have hb := Nat.le_of_ble_eq_true (h.resolve_left (by decide))
  rw [card_cos false (X := cosC false (el a) (el a))
    (P := fun y => y * el a = el a * y ∧ y * el a = el a * y) (fun y => Iff.rfl)
    (f := fun q => strictB (L34PT.T q) fun y => CFSG.KC.L34Tw.commK (L34PT.T a) y) (fun q hq => by
      rw [sB, hrt.comm (el_spec hq).2]
      exact ⟨fun e => ⟨e.symm, e.symm⟩, fun e => e.1.symm⟩)]
  exact hb

theorem concXFacts : ConcXFacts where
  cent := cent_fact
  inv := inv_fact
  uni := uni_fact
  big := big_fact
  qcard := fun _ hv hvv i => (q_facts hv hvv i).1
  qinv := fun _ hv hvv i => (q_facts hv hvv i).2.1
  qsq := fun _ hv hvv i => (q_facts hv hvv i).2.2
  pcard := fun _ ht htt ht1 _ hu huu htu => (p_facts ht htt ht1 hu huu htu).1
  pinv := fun _ ht htt ht1 _ hu huu htu => (p_facts ht htt ht1 hu huu htu).2.1
  psq := fun _ ht htt ht1 _ hu huu htu => (p_facts ht htt ht1 hu huu htu).2.2

theorem facts33211
    (h₁ : ∀ x, x ∈ X1 ↔ x ∈ Pw ∧ cc x ∈ U1) (h₂ : ∀ x, x ∈ X2 ↔ x ∈ Pw ∧ cc x ∈ U2) :
    ConcX X1 ∧ ConcX X2 :=
  ⟨raHyp.concX concXFacts (Or.inl rfl) h₁, raHyp.concX concXFacts (Or.inr rfl) h₂⟩

end CertificateChecks.KernelLC.L34Tw

end
