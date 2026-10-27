module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtXK
public import CFSG.Sporadic.SuzRecog.SuzL34.Facts
public import CFSG.Certificates.Kernel.Spor.BTupSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BTupISound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtXG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.SuzL34Cert
open CertificateChecks.KernelSpor.SuzBtXF CertificateChecks.KernelSpor.SuzBtXK

local notation "pg4" => pg 4 (mask 4)

theorem permC_val {n : Nat} {t : Array Nat}
    (h : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j) (x : Fin n) :
    ((permC n t x : Fin n) : Nat) = t[x.val]! := by
  rw [permC, @dite_eq_left_of_eq_true _ _ (Classical.propDecidable _) _ _ (eq_true h)]
  rfl

noncomputable def gpX (i j : Nat) : Equiv.Perm (Fin 16) :=
  if j = 0 then tabPerm16 xA else tabPerm16 (xBs[i]!)

theorem gpX_zero (i : Nat) : gpX i 0 = tabPerm16 xA := if_pos rfl

theorem gpX_one (i : Nat) : gpX i 1 = tabPerm16 (xBs[i]!) := if_neg one_ne_zero

theorem genSub_eq (i : Nat) : genSub 16 2 (gpX i) = X16 i := by
  unfold genSub X16
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    · exact Or.inl (gpX_zero i)
    · exact Or.inr (gpX_one i)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, gpX_zero i⟩
    · exact ⟨1, by norm_num, gpX_one i⟩

theorem inj_xA : (∀ i < 16, xA[i]! < 16) ∧ ∀ i < 16, ∀ j < 16, xA[i]! = xA[j]! → i = j := by
  decide +kernel

theorem inj_xB {i : Nat} (hi : i < 4) :
    (∀ k < 16, (xBs[i]!)[k]! < 16) ∧ ∀ k < 16, ∀ l < 16, (xBs[i]!)[k]! = (xBs[i]!)[l]! → k = l := by
  interval_cases i <;> decide +kernel

theorem inj_tb {j : Nat} (hj : j < 2) :
    (∀ k < 16, (tbarTabs[j]!)[k]! < 16) ∧
      ∀ k < 16, ∀ l < 16, (tbarTabs[j]!)[k]! = (tbarTabs[j]!)[l]! → k = l := by
  interval_cases j <;> decide +kernel

theorem tb_tab {j : Nat} (hj : j < 2) (p : Fin 16) :
    pg4 (TB j) p = ((tabPerm16 (tbarTabs[j]!) p : Fin 16) : Nat) := by
  rw [tabPerm16, permC_val (inj_tb hj)]
  revert p
  interval_cases j <;> decide +kernel

structure Rec (X : Subgroup (Equiv.Perm (Fin 16))) (K : Nat → Nat) : Prop where
  mem : ∀ s < 60, ∃ h ∈ X, ∀ p : Fin 16, pg4 (el K s) p = h p
  cover : ∀ h ∈ X, ∃ s < 60, ∀ p : Fin 16, pg4 (el K s) p = h p
  inj : ∀ s < 60, ∀ t < 60, (∀ p : Fin 16, pg4 (el K s) p = pg4 (el K t) p) → s = t
  canon : ∀ s < 60, el K s >>> (16 * 4) = 0

theorem rec_of {i : Nat} {G K R POS : Nat → Nat} {B cnt : Nat}
    (hg : ∀ j < 2, ∀ x : Fin 16, pg4 (G j) x = gpX i j x) (hb : ∀ t : Fin 16, pg4 B t = t)
    (hc : cnt = 60) (hd : btHdK cnt = true)
    (hp : ∀ s < cnt, btPtK 16 4 (mask 4) 16 64 (mask 64) 2 cnt B G K R POS s = true) :
    Rec (X16 i) K where
  mem s hs := by
    obtain ⟨h, hh, he⟩ := btKey_mem (b := fun t => t) hg hb hp (hc ▸ hs)
    exact ⟨h, genSub_eq i ▸ hh, he⟩
  cover h hh := by
    obtain ⟨s, hs, he⟩ := btKey_cover (b := fun t => t) hg hb hp hd ((genSub_eq i).symm ▸ hh)
    exact ⟨s, hc ▸ hs, he⟩
  inj s hs t ht he := btKey_inj (by norm_num) hp (hc ▸ hs) (hc ▸ ht) he
  canon s hs := (ptFacts (hp s (hc ▸ hs))).canon

section Elements

variable {X : Subgroup (Equiv.Perm (Fin 16))} {K : Nat → Nat}

noncomputable def elt (R : Rec X K) (s : Nat) : Equiv.Perm (Fin 16) :=
  if h : s < 60 then Classical.choose (R.mem s h) else 1

variable (R : Rec X K)

theorem elt_mem {s : Nat} (hs : s < 60) : elt R s ∈ X := by
  unfold elt
  rw [dif_pos hs]
  exact (Classical.choose_spec (R.mem s hs)).1

theorem elt_key {s : Nat} (hs : s < 60) (p : Fin 16) : pg4 (el K s) p = elt R s p := by
  unfold elt
  rw [dif_pos hs]
  exact (Classical.choose_spec (R.mem s hs)).2 p

theorem elt_of {s : Nat} (hs : s < 60) {x : Equiv.Perm (Fin 16)}
    (he : ∀ p : Fin 16, pg4 (el K s) p = x p) : elt R s = x :=
  Equiv.ext fun p => Fin.ext (by rw [← elt_key R hs p, he p])

theorem elt_cover {x : Equiv.Perm (Fin 16)} (hx : x ∈ X) : ∃ s < 60, elt R s = x := by
  obtain ⟨s, hs, he⟩ := R.cover x hx
  exact ⟨s, hs, elt_of R hs he⟩

theorem elt_inj {s t : Nat} (hs : s < 60) (ht : t < 60) (h : elt R s = elt R t) : s = t :=
  R.inj s hs t ht fun p => by rw [elt_key R hs, elt_key R ht, h]

theorem card_states (P : Equiv.Perm (Fin 16) → Prop) (f : Nat → Bool)
    (hP : ∀ x, P x → x ∈ X) (hf : ∀ s < 60, f s = true ↔ P (elt R s)) :
    Nat.card {x // P x} = btCntN 60 f := by
  rw [btCntN_eq]
  set T := (Finset.range 60).filter (fun i => f i = true)
  have hT : T.card = Nat.card {i : Nat // i ∈ T} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hT]
  have hmemT : ∀ i ∈ T, i < 60 ∧ f i = true := fun i hi => by
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact hi
  let φ : {i : Nat // i ∈ T} → {x // P x} := fun i =>
    ⟨elt R i.1, (hf i.1 (hmemT i.1 i.2).1).1 (hmemT i.1 i.2).2⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun i j e => Subtype.ext (elt_inj R (hmemT i.1 i.2).1 (hmemT j.1 j.2).1
      (congrArg Subtype.val e)), fun x => ?_⟩
    obtain ⟨i, hi, he⟩ := elt_cover R (hP x.1 x.2)
    have hiT : i ∈ T := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, (hf i hi).2 (he ▸ x.2)⟩
    exact ⟨⟨i, hiT⟩, Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective φ hbij)).symm

theorem pw_elt {s : Nat} (hs : s < 60) (e : Nat) (p : Fin 16) :
    pw (el K s) e p = ((elt R s ^ e) p : Nat) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    have h : pw (el K s) (e + 1) p = pg4 (el K s) (pw (el K s) e p) := rfl
    rw [h, ih, elt_key R hs, pow_succ', Equiv.Perm.mul_apply]

theorem isOne_iff {s : Nat} (hs : s < 60) (e : Nat) :
    isOne (el K s) e = true ↔ elt R s ^ e = 1 := by
  unfold isOne
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h
    refine Equiv.ext fun p => Fin.ext ?_
    rw [← pw_elt R hs e p, Equiv.Perm.one_apply]
    exact Nat.eq_of_beq_eq_true (h p.val p.2)
  · intro h p hp
    have e1 := pw_elt R hs e ⟨p, hp⟩
    rw [h, Equiv.Perm.one_apply] at e1
    rw [e1]
    exact Nat.beq_refl p

theorem isOne_one_iff {s : Nat} (hs : s < 60) : isOne (el K s) 1 = true ↔ elt R s = 1 := by
  rw [isOne_iff R hs, pow_one]

theorem orderOf_prime_iff {s : Nat} (hs : s < 60) {q : Nat} [Fact q.Prime] :
    orderOf (elt R s) = q ↔ isOne (el K s) q = true ∧ isOne (el K s) 1 = false := by
  rw [orderOf_eq_prime_iff, isOne_iff R hs, ← Bool.not_eq_true, isOne_one_iff R hs]

theorem isInvT_iff {s : Nat} (hs : s < 60) : isInvT (el K s) = true ↔ orderOf (elt R s) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold isInvT
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, orderOf_prime_iff R hs, Bool.not_eq_true',
    and_comm]

end Elements

theorem part1 {i : Nat} {K : Nat → Nat} (R : Rec (X16 i) K)
    (hTb : allN 2 (fun j => memK K 60 (TB j)) = true)
    (hFx : allN 60 (fun s => fxK (btKey 64 (mask 64) K s)) = true) :
    Nat.card (X16 i) = 60 ∧ Tbar16 ≤ X16 i ∧
      ∀ x ∈ X16 i, (orderOf x = 3 ∨ orderOf x = 5) → ∀ j : Fin 16, x j = j → j = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := card_states R (· ∈ X16 i) (fun _ => true) (fun _ h => h)
      (fun s hs => iff_of_true rfl (elt_mem R hs))
    have e : btCntN 60 (fun _ => true) = 60 := by decide
    rw [e] at h
    exact h
  · unfold Tbar16
    rw [Subgroup.closure_le]
    have hT : ∀ j < 2, tabPerm16 (tbarTabs[j]!) ∈ X16 i := by
      intro j hj
      have hm := CFSG.KS.Raw.Orb.allN_iff.1 hTb j hj
      unfold memK at hm
      rw [Bool.not_eq_true', ← Bool.not_eq_true, CFSG.KS.Raw.Orb.allN_iff] at hm
      push Not at hm
      obtain ⟨s, hs, hk⟩ := hm
      have hk' : el K s = TB j := by
        cases h : Nat.beq (btKey 64 (mask 64) K s) (TB j)
        · rw [h] at hk
          exact absurd rfl hk
        · exact Nat.eq_of_beq_eq_true h
      rw [← elt_of R hs (x := tabPerm16 (tbarTabs[j]!)) (fun p => by rw [hk', tb_tab hj p])]
      exact elt_mem R hs
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hT 0 (by norm_num)
    · exact hT 1 (by norm_num)
  · intro x hx ho j hj
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨s, hs, rfl⟩ := elt_cover R hx
    have hf := CFSG.KS.Raw.Orb.allN_iff.1 hFx s hs
    have hc : bAnd(Bool.not (isOne (el K s) 1), Bool.rec (motive := fun _ => Bool)
        (isOne (el K s) 5) true (isOne (el K s) 3)) = true := by
      rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true]
      rcases ho with h3 | h5
      · obtain ⟨h1, h2⟩ := (orderOf_prime_iff R hs).1 h3
        rw [h2, h1]
        exact ⟨rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := (orderOf_prime_iff R hs).1 h5
        rw [h2]
        refine ⟨rfl, ?_⟩
        cases h : isOne (el K s) 3
        · exact h1
        · rfl
    unfold fxK at hf
    change bIf(bAnd(Bool.not (isOne (el K s) 1), Bool.rec (motive := fun _ => Bool)
        (isOne (el K s) 5) true (isOne (el K s) 3)), _, true) = true at hf
    rw [hc] at hf
    by_contra hj0
    obtain ⟨p, hp⟩ : ∃ p, j.val = p + 1 := ⟨j.val - 1, by
      have : j.val ≠ 0 := fun e => hj0 (Fin.ext e)
      omega⟩
    have h1 := CFSG.KS.Raw.Orb.allN_iff.1 hf p (by omega)
    have h2 : pg4 (btKey 64 (mask 64) K s) (Nat.succ p) = Nat.succ p := by
      have e := elt_key R hs j
      rw [hj, hp] at e
      exact e
    rw [h2, Nat.beq_refl] at h1
    exact Bool.noConfusion h1

def Tb (T : Nat) (x : Equiv.Perm (Fin 16)) : Prop := T >>> (16 * 4) = 0 ∧ ∀ p : Fin 16, pg4 T p = x p

theorem tb_el {X : Subgroup (Equiv.Perm (Fin 16))} {K : Nat → Nat} (R : Rec X K) {s : Nat}
    (hs : s < 60) : Tb (el K s) (elt R s) := ⟨R.canon s hs, elt_key R hs⟩

theorem tb_cmpT {a b : Nat} {x y : Equiv.Perm (Fin 16)} (ha : Tb a x) (hb : Tb b y) :
    Tb (cmpT a b) (x * y) := by
  refine ⟨CFSG.KS.PF.pcomp_shr a b (by norm_num) (by norm_num), fun p => ?_⟩
  unfold cmpT
  rw [CFSG.KS.PF.pg_pcomp (by norm_num) p.2, hb.2 p, ha.2 (y p), Equiv.Perm.mul_apply]

theorem tb_eq_iff {a b : Nat} {x y : Equiv.Perm (Fin 16)} (ha : Tb a x) (hb : Tb b y) :
    a = b ↔ x = y := by
  constructor
  · intro e
    subst e
    exact Equiv.ext fun p => Fin.ext (by rw [← ha.2 p, ← hb.2 p])
  · intro e
    subst e
    exact CFSG.KS.PF.eq_of_fields (n := 16) (w := 4) (by norm_num) ha.1 hb.1
      fun i hi => by rw [ha.2 ⟨i, hi⟩, hb.2 ⟨i, hi⟩]

theorem tb_beq_iff {a b : Nat} {x y : Equiv.Perm (Fin 16)} (ha : Tb a x) (hb : Tb b y) :
    Nat.beq a b = true ↔ x = y := by
  rw [Nat.beq_eq, tb_eq_iff ha hb]

theorem anyN_iff {n : Nat} {f : Nat → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  unfold anyN
  rw [Bool.not_eq_true', ← Bool.not_eq_true, CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h fun i hi => by rw [Bool.not_eq_true']; simpa using h' i hi
  · rintro ⟨i, hi, h⟩ h'
    have := h' i hi
    rw [h] at this
    exact Bool.noConfusion this

section Four

variable {X : Subgroup (Equiv.Perm (Fin 16))} {K : Nat → Nat} (R : Rec X K) {VP : Nat}

def Vset (k : Nat) : Set (Equiv.Perm (Fin 16)) :=
  {x | x = 1 ∨ ∃ j < 3, x = elt R (vS VP k j)}

structure VFacts (R : Rec X K) (VP : Nat) : Prop where
  lt : ∀ k < 5, ∀ j < 3, vS VP k j < 60
  inv : ∀ k < 5, ∀ j < 3, orderOf (elt R (vS VP k j)) = 2
  dist : ∀ k < 5, ∀ j < 3, ∀ l < 5, ∀ j' < 3, vS VP k j = vS VP l j' → k = l ∧ j = j'
  mul : ∀ k < 5, ∀ j < 3, ∀ j' < 3, j ≠ j' →
    elt R (vS VP k j) * elt R (vS VP k j') = elt R (vS VP k (3 - (j + j')))

theorem vS_eq (k j : Nat) : vS VP k j = vF VP (3 * k + j) := rfl

theorem vFacts (hV : vK K VP = true) : VFacts R VP := by
  unfold vK at hV
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hV
  obtain ⟨h1, h2⟩ := hV
  have hm : ∀ m < 15, vF VP m < 60 ∧ isInvT (el K (vF VP m)) = true ∧
      ∀ m' < 15, m ≠ m' → vF VP m ≠ vF VP m' := by
    intro m hm
    have h := CFSG.KS.Raw.Orb.allN_iff.1 h1 m hm
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.bAnd_eq,
      Bool.and_eq_true] at h
    refine ⟨Nat.blt_eq.mp h.1, h.2.1, fun m' hm' hne e => ?_⟩
    have h' := CFSG.KS.Raw.Orb.allN_iff.1 h.2.2 m' hm'
    rw [CFSG.KS.Raw.Orb.bIf_eq, if_neg (by rw [Nat.beq_eq]; exact hne), e, Nat.beq_refl] at h'
    exact Bool.noConfusion h'
  have hlt : ∀ k < 5, ∀ j < 3, vS VP k j < 60 := fun k hk j hj => by
    rw [vS_eq]
    exact (hm _ (by omega)).1
  refine ⟨hlt, fun k hk j hj => ?_, fun k hk j hj l hl j' hj' e => ?_, fun k hk j hj j' hj' hne => ?_⟩
  · rw [← isInvT_iff R (hlt k hk j hj), vS_eq]
    exact (hm _ (by omega)).2.1
  · rw [vS_eq, vS_eq] at e
    by_contra hne
    exact (hm _ (by omega)).2.2 _ (by omega) (by omega) e
  · have h := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1
      (CFSG.KS.Raw.Orb.allN_iff.1 h2 k hk) j hj) j' hj'
    rw [CFSG.KS.Raw.Orb.bIf_eq, if_neg (by rw [Nat.beq_eq]; exact hne)] at h
    have hl3 : 3 - (j + j') < 3 := by omega
    exact (tb_beq_iff (tb_cmpT (tb_el R (hlt k hk j hj)) (tb_el R (hlt k hk j' hj')))
      (tb_el R (hlt k hk _ hl3))).1 h

variable {R}

theorem elt_ne_one (F : VFacts R VP) {k j : Nat} (hk : k < 5) (hj : j < 3) :
    elt R (vS VP k j) ≠ 1 := fun e => by
  have h := F.inv k hk j hj
  rw [e, orderOf_one] at h
  exact absurd h (by norm_num)

theorem elt_sq (F : VFacts R VP) {k j : Nat} (hk : k < 5) (hj : j < 3) :
    elt R (vS VP k j) * elt R (vS VP k j) = 1 := by
  rw [← pow_two, ← F.inv k hk j hj]
  exact pow_orderOf_eq_one _

theorem elt_vS_inj (F : VFacts R VP) {k j l j' : Nat} (hk : k < 5) (hj : j < 3) (hl : l < 5)
    (hj' : j' < 3) (e : elt R (vS VP k j) = elt R (vS VP l j')) : k = l ∧ j = j' :=
  F.dist k hk j hj l hl j' hj' (elt_inj R (F.lt k hk j hj) (F.lt l hl j' hj') e)

def Vsub (F : VFacts R VP) (k : Nat) (hk : k < 5) : Subgroup (Equiv.Perm (Fin 16)) where
  carrier := Vset R (VP := VP) k
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | ⟨j, hj, rfl⟩) (rfl | ⟨j', hj', rfl⟩)
    · exact Or.inl (one_mul 1)
    · rw [one_mul]
      exact Or.inr ⟨j', hj', rfl⟩
    · rw [mul_one]
      exact Or.inr ⟨j, hj, rfl⟩
    · by_cases e : j = j'
      · subst e
        exact Or.inl (elt_sq F hk hj)
      · exact Or.inr ⟨3 - (j + j'), by omega, F.mul k hk j hj j' hj' e⟩
  inv_mem' := by
    rintro a (rfl | ⟨j, hj, rfl⟩)
    · exact Or.inl inv_one
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [inv_eq_iff_mul_eq_one]
      exact elt_sq F hk hj

theorem mem_Vsub (F : VFacts R VP) {k : Nat} (hk : k < 5) {x : Equiv.Perm (Fin 16)} :
    x ∈ Vsub F k hk ↔ x = 1 ∨ ∃ j < 3, x = elt R (vS VP k j) := Iff.rfl

theorem Vsub_le (F : VFacts R VP) {k : Nat} (hk : k < 5) : Vsub F k hk ≤ X := by
  rintro x (rfl | ⟨j, hj, rfl⟩)
  · exact X.one_mem
  · exact elt_mem R (F.lt k hk j hj)

theorem card_Vsub (F : VFacts R VP) {k : Nat} (hk : k < 5) : Nat.card (Vsub F k hk) = 4 := by
  classical
  have e : ((Vsub F k hk : Subgroup _) : Set (Equiv.Perm (Fin 16))) =
      ↑({1, elt R (vS VP k 0), elt R (vS VP k 1), elt R (vS VP k 2)} :
        Finset (Equiv.Perm (Fin 16))) := by
    ext x
    simp only [SetLike.mem_coe, mem_Vsub, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl h
      · interval_cases j
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr ⟨0, by norm_num, h⟩
      · exact Or.inr ⟨1, by norm_num, h⟩
      · exact Or.inr ⟨2, by norm_num, h⟩
  have hc : Nat.card (Vsub F k hk) = Nat.card ((Vsub F k hk : Subgroup _) :
      Set (Equiv.Perm (Fin 16))) := rfl
  rw [hc, e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have n1 : ∀ j < 3, ∀ j' < 3, j ≠ j' → elt R (vS VP k j) ≠ elt R (vS VP k j') :=
    fun j hj j' hj' hne e => hne (elt_vS_inj F hk hj hk hj' e).2
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · exact n1 1 (by norm_num) 2 (by norm_num) (by norm_num)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨n1 0 (by norm_num) 1 (by norm_num) (by norm_num),
      n1 0 (by norm_num) 2 (by norm_num) (by norm_num)⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => elt_ne_one F hk (by norm_num : 0 < 3) e.symm,
      fun e => elt_ne_one F hk (by norm_num : 1 < 3) e.symm,
      fun e => elt_ne_one F hk (by norm_num : 2 < 3) e.symm⟩

theorem Vsub_inf (F : VFacts R VP) {k l : Nat} (hk : k < 5) (hl : l < 5) (hne : k ≠ l) :
    Vsub F k hk ⊓ Vsub F l hl = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  rcases hx1 with h | ⟨j, hj, rfl⟩
  · exact h
  · rcases hx2 with h | ⟨j', hj', h⟩
    · exact h
    · exact absurd (elt_vS_inj F hk hj hl hj' h).1 hne

theorem conj_iff {y x z : Equiv.Perm (Fin 16)} : y * x * y⁻¹ = z ↔ y * x = z * y :=
  mul_inv_eq_iff_eq_mul

theorem map_le_of (F : VFacts R VP) {k l : Nat} (hk : k < 5) (hl : l < 5)
    {y : Equiv.Perm (Fin 16)}
    (h : ∀ j < 3, ∃ j' < 3, y * elt R (vS VP k j) = elt R (vS VP l j') * y) :
    (Vsub F k hk).map (MulAut.conj y).toMonoidHom ≤ Vsub F l hl := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z = 1 ∨ ∃ j < 3, z = elt R (vS VP k j) := hz
  rcases hz' with rfl | ⟨j, hj, rfl⟩
  · rw [map_one]
    exact (Vsub F l hl).one_mem
  · obtain ⟨j', hj', e⟩ := h j hj
    refine Or.inr ⟨j', hj', ?_⟩
    change y * elt R (vS VP k j) * y⁻¹ = _
    exact conj_iff.2 e

theorem map_eq_of (F : VFacts R VP) {k l : Nat} (hk : k < 5) (hl : l < 5)
    {y : Equiv.Perm (Fin 16)}
    (h : ∀ j < 3, ∃ j' < 3, y * elt R (vS VP k j) = elt R (vS VP l j') * y) :
    (Vsub F k hk).map (MulAut.conj y).toMonoidHom = Vsub F l hl :=
  Subgroup.eq_of_le_of_card_ge (map_le_of F hk hl h) (by
    rw [Subgroup.card_map_of_injective (fun a b e => (MulAut.conj y).injective e), card_Vsub,
      card_Vsub])

theorem mem_normalizer_iff (F : VFacts R VP) {k : Nat} (hk : k < 5) {y : Equiv.Perm (Fin 16)} :
    y ∈ Subgroup.normalizer ((Vsub F k hk : Subgroup _) : Set (Equiv.Perm (Fin 16))) ↔
      ∀ j < 3, ∃ j' < 3, y * elt R (vS VP k j) = elt R (vS VP k j') * y := by
  constructor
  · intro hy j hj
    have hm : y * elt R (vS VP k j) * y⁻¹ ∈ ((Vsub F k hk : Subgroup _) : Set _) :=
      (Subgroup.mem_set_normalizer_iff.1 hy _).1 (Or.inr ⟨j, hj, rfl⟩)
    have hm' : y * elt R (vS VP k j) * y⁻¹ = 1 ∨
        ∃ j' < 3, y * elt R (vS VP k j) * y⁻¹ = elt R (vS VP k j') := hm
    rcases hm' with h1 | ⟨j', hj', e⟩
    · exact absurd (by simpa using h1) (elt_ne_one F hk hj)
    · exact ⟨j', hj', conj_iff.1 e⟩
  · intro h
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have e := congrArg SetLike.coe (map_eq_of F hk hk h)
    rw [Subgroup.coe_map] at e
    exact e

end Four

theorem brec_iff (b c : Bool) :
    Bool.rec (motive := fun _ => Bool) (Bool.not b) b c = true ↔ (c = true ↔ b = true) := by
  cases b <;> cases c <;> decide

theorem bor4_iff (a b c d : Bool) :
    bIf(a, true, bIf(b, true, bIf(c, true, d))) = true ↔
      a = true ∨ b = true ∨ c = true ∨ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem bor2_iff (a b : Bool) : bIf(a, true, b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem card_fin5 (P : Fin 5 → Prop) (f : Nat → Bool) (hf : ∀ k : Fin 5, f k.val = true ↔ P k) :
    Nat.card {k : Fin 5 // P k} = btCntN 5 f := by
  classical
  rw [btCntN_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun k _ => k.val) (fun k hk => ?_) (fun a _ b _ e => Fin.ext e)
    (fun i hi => ?_)
  · rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_range.2 k.isLt, (hf k).2 hk.2⟩
  · rw [Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨⟨i, hi.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hf ⟨i, hi.1⟩).1 hi.2⟩, rfl⟩

section F11

variable {X : Subgroup (Equiv.Perm (Fin 16))} {K : Nat → Nat} {R : Rec X K} {VP WP : Nat}

theorem nrm_iff (F : VFacts R VP) {k : Nat} (hk : k < 5) {a : Nat} {x : Equiv.Perm (Fin 16)}
    (ha : Tb a x) :
    nrm K VP a k = true ↔ ∀ j < 3, ∃ j' < 3, x * elt R (vS VP k j) = elt R (vS VP k j') * x := by
  unfold nrm
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall₂_congr fun j hj => ?_
  rw [CFSG.KS.Raw.Orb.strictB_eq, anyN_iff]
  refine exists_congr fun j' => and_congr_right fun hj' => ?_
  exact tb_beq_iff (tb_cmpT ha (tb_el R (F.lt k hk j hj))) (tb_cmpT (tb_el R (F.lt k hk j' hj')) ha)

theorem cnj_iff (F : VFacts R VP) {k l : Nat} (hk : k < 5) (hl : l < 5) {a : Nat}
    {x : Equiv.Perm (Fin 16)} (ha : Tb a x) :
    cnj K VP a k l = true ↔ ∀ j < 3, ∃ j' < 3, x * elt R (vS VP k j) = elt R (vS VP l j') * x := by
  unfold cnj
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall₂_congr fun j hj => ?_
  rw [CFSG.KS.Raw.Orb.strictB_eq, anyN_iff]
  refine exists_congr fun j' => and_congr_right fun hj' => ?_
  exact tb_beq_iff (tb_cmpT ha (tb_el R (F.lt k hk j hj))) (tb_cmpT (tb_el R (F.lt l hl j' hj')) ha)

theorem inV_iff {k s : Nat} : inV VP k s = true ↔ ∃ j < 3, s = vS VP k j := by
  unfold inV
  rw [anyN_iff]
  exact exists_congr fun j => and_congr_right fun _ => by rw [Nat.beq_eq]

theorem cv_facts (F : VFacts R VP) (hC : cvK K VP = true) :
    (∀ s < 60, orderOf (elt R s) = 2 → ∃ k < 5, ∃ j < 3, s = vS VP k j) ∧
    (∀ k < 5, ∀ j < 3, ∀ s < 60, (orderOf (elt R s) = 2 ∧
      elt R s * elt R (vS VP k j) = elt R (vS VP k j) * elt R s) ↔ ∃ j' < 3, s = vS VP k j') := by
  have hs : ∀ s < 60, _ := fun s hs => CFSG.KS.Raw.Orb.allN_iff.1 hC s hs
  refine ⟨fun s hs2 ho => ?_, fun k hk j hj s hs2 => ?_⟩
  · have h := hs s hs2
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
      CFSG.KS.Raw.Orb.bIf_eq, if_pos ((isInvT_iff R hs2).2 ho), anyN_iff] at h
    obtain ⟨k, hk, hv⟩ := h.1
    exact ⟨k, hk, inV_iff.1 hv⟩
  · have h := hs s hs2
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h.2 k hk) j hj
    rw [CFSG.KS.Raw.Orb.strictB_eq, brec_iff, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
      isInvT_iff R hs2, tb_beq_iff (tb_cmpT (tb_el R hs2) (tb_el R (F.lt k hk j hj)))
        (tb_cmpT (tb_el R (F.lt k hk j hj)) (tb_el R hs2)), inV_iff] at h2
    exact h2

theorem card_inv (R : Rec X K) (hI : invK K 15 = true) :
    Nat.card {u : X // orderOf (u : Equiv.Perm (Fin 16)) = 2} = 15 := by
  rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ X)
    (fun x : Equiv.Perm (Fin 16) => orderOf x = 2)).symm]
  rw [card_states R (fun x => x ∈ X ∧ orderOf x = 2) (fun s => isInvT (el K s)) (fun _ h => h.1)
    (fun s hs => by rw [isInvT_iff R hs]; exact ⟨fun h => ⟨elt_mem R hs, h⟩, fun h => h.2⟩)]
  exact Nat.eq_of_beq_eq_true hI

theorem V4Sub_eq (F : VFacts R VP) (hC : cvK K VP = true) {k j : Nat} (hk : k < 5)
    (hj : j < 3) : V4Sub X (elt R (vS VP k j)) = Vsub F k hk := by
  have hcv := (cv_facts F hC).2 k hk j hj
  unfold V4Sub
  have e : (({1, elt R (vS VP k j)} : Set (Equiv.Perm (Fin 16))) ∪
      {v | v ∈ X ∧ orderOf v = 2 ∧ Commute v (elt R (vS VP k j))}) =
      ((Vsub F k hk : Subgroup _) : Set (Equiv.Perm (Fin 16))) := by
    ext v
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      SetLike.mem_coe]
    rw [mem_Vsub]
    constructor
    · rintro ((h | h) | ⟨hv, ho, hc⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, h⟩
      · obtain ⟨s, hs, rfl⟩ := elt_cover R hv
        obtain ⟨j', hj', rfl⟩ := (hcv s hs).1 ⟨ho, hc⟩
        exact Or.inr ⟨j', hj', rfl⟩
    · rintro (h | ⟨j', hj', rfl⟩)
      · exact Or.inl (Or.inl h)
      · refine Or.inr ⟨elt_mem R (F.lt k hk j' hj'), ?_⟩
        have := ((hcv _ (F.lt k hk j' hj')).2 ⟨j', hj', rfl⟩)
        exact ⟨this.1, this.2⟩
  rw [e, Subgroup.closure_eq]

theorem f11_of (R : Rec X K) (hI : invK K 15 = true) (hV : vK K VP = true)
    (hC : cvK K VP = true) (h5 : o5K K 10 = true) (h3 : o3K K VP WP = true)
    (hN : nK K VP 12 = true) :
    Nat.card {u : X // orderOf (u : Equiv.Perm (Fin 16)) = 2} = 15 ∧
      (∀ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 →
        Nat.card (V4Sub X (u : Equiv.Perm (Fin 16))) = 4) ∧
      ∃ V : Fin 5 → Subgroup (Equiv.Perm (Fin 16)),
        (∀ k, V k ≤ X) ∧
          (∀ k, Nat.card (V k) = 4) ∧
          (∀ k l, k ≠ l → V k ≠ V l) ∧
          (∀ k l, k ≠ l → V k ⊓ V l = ⊥) ∧
          (∀ k, ∃ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 ∧
            V k = V4Sub X (u : Equiv.Perm (Fin 16))) ∧
          (∀ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 →
            ∃ k, V k = V4Sub X (u : Equiv.Perm (Fin 16))) ∧
          (∀ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 →
            ∃ k, (u : Equiv.Perm (Fin 16)) ∈ V k) ∧
          (∀ x : X, orderOf (x : Equiv.Perm (Fin 16)) = 5 →
            Nat.card {y : X // (y * x * y⁻¹ : X) ∈ ({x, x ^ 2, x ^ 3, x ^ 4} : Set X)} = 10) ∧
          (∀ x : X, orderOf (x : Equiv.Perm (Fin 16)) = 3 →
            Nat.card {k : Fin 5 // (x : Equiv.Perm (Fin 16)) ∈
                Subgroup.normalizer (V k : Set (Equiv.Perm (Fin 16)))} = 2 ∧
              ∃ y : X, orderOf (y : Equiv.Perm (Fin 16)) = 2 ∧
                (y * x * y⁻¹ : X) ∈ ({x, x ^ 2} : Set X) ∧
                ∃ k l : Fin 5, k ≠ l ∧
                  (x : Equiv.Perm (Fin 16)) ∈
                    Subgroup.normalizer (V k : Set (Equiv.Perm (Fin 16))) ∧
                  (x : Equiv.Perm (Fin 16)) ∈
                    Subgroup.normalizer (V l : Set (Equiv.Perm (Fin 16))) ∧
                  (V k).map (MulAut.conj (y : Equiv.Perm (Fin 16))).toMonoidHom = V l) ∧
          (∀ k, Nat.card ↥(Subgroup.normalizer (V k : Set (Equiv.Perm (Fin 16))) ⊓ X) = 12) := by
  have F := vFacts R hV
  obtain ⟨hcov, hcv⟩ := cv_facts F hC
  have hinv : ∀ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 →
      ∃ k < 5, ∃ j < 3, (u : Equiv.Perm (Fin 16)) = elt R (vS VP k j) := by
    intro u hu
    obtain ⟨s, hs, hsu⟩ := elt_cover R u.2
    rw [← hsu] at hu
    obtain ⟨k, hk, j, hj, rfl⟩ := hcov s hs hu
    exact ⟨k, hk, j, hj, hsu.symm⟩
  let V : Fin 5 → Subgroup (Equiv.Perm (Fin 16)) := fun k => Vsub F k.val k.isLt
  refine ⟨card_inv R hI, fun u hu => ?_, V, fun k => Vsub_le F k.isLt, fun k => card_Vsub F k.isLt,
    fun k l hne e => ?_, fun k l hne => Vsub_inf F k.isLt l.isLt (fun e => hne (Fin.ext e)),
    fun k => ?_, fun u hu => ?_, fun u hu => ?_, fun x hx => ?_, fun x hx => ?_, fun k => ?_⟩
  · obtain ⟨k, hk, j, hj, e⟩ := hinv u hu
    rw [e, V4Sub_eq F hC hk hj, card_Vsub]
  · have h := Vsub_inf F k.isLt l.isLt (fun e => hne (Fin.ext e))
    change V k ⊓ V l = ⊥ at h
    rw [e, inf_idem] at h
    have hc := card_Vsub F l.isLt
    change Nat.card (V l) = 4 at hc
    rw [h, Subgroup.card_bot] at hc
    exact absurd hc (by norm_num)
  · refine ⟨⟨elt R (vS VP k.val 0), elt_mem R (F.lt k.val k.isLt 0 (by norm_num))⟩,
      F.inv k.val k.isLt 0 (by norm_num), ?_⟩
    exact (V4Sub_eq F hC k.isLt (by norm_num : 0 < 3)).symm
  · obtain ⟨k, hk, j, hj, e⟩ := hinv u hu
    exact ⟨⟨k, hk⟩, by rw [e, V4Sub_eq F hC hk hj]⟩
  · obtain ⟨k, hk, j, hj, e⟩ := hinv u hu
    exact ⟨⟨k, hk⟩, Or.inr ⟨j, hj, e⟩⟩
  ·
    obtain ⟨s, hs, hsx⟩ := elt_cover R x.2
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [← hsx] at hx
    obtain ⟨h5a, h1a⟩ := (orderOf_prime_iff R hs).1 hx
    have h := CFSG.KS.Raw.Orb.allN_iff.1 h5 s hs
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq, h1a, h5a,
      Bool.not_false, Bool.true_and, if_pos rfl, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq,
      CFSG.KS.Raw.Orb.strictB_eq] at h
    have tx := tb_el R hs
    have t2 := tb_cmpT tx tx
    have t3 := tb_cmpT tx t2
    have t4 := tb_cmpT tx t3
    have e : Nat.card {y : X // (y * x * y⁻¹ : X) ∈ ({x, x ^ 2, x ^ 3, x ^ 4} : Set X)} =
        Nat.card {z : Equiv.Perm (Fin 16) // z ∈ X ∧ (z * elt R s = elt R s * z ∨
          z * elt R s = (elt R s * elt R s) * z ∨
          z * elt R s = (elt R s * (elt R s * elt R s)) * z ∨
          z * elt R s = (elt R s * (elt R s * (elt R s * elt R s))) * z)} := by
      rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ X) _)]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_pow, hsx, conj_iff, pow_succ', pow_zero, mul_one]
    rw [e, card_states R _ (fun t => strictB (el K t) (fun Y => strictB (cmpT Y (el K s))
      (fun YX => bIf(Nat.beq YX (cmpT (el K s) Y), true, bIf(Nat.beq YX
        (cmpT (cmpT (el K s) (el K s)) Y), true, bIf(Nat.beq YX (cmpT (cmpT (el K s)
          (cmpT (el K s) (el K s))) Y), true, Nat.beq YX (cmpT (cmpT (el K s) (cmpT (el K s)
            (cmpT (el K s) (el K s)))) Y))))))) (fun _ h => h.1) (fun t ht => ?_)]
    · exact Nat.eq_of_beq_eq_true h
    · have ty := tb_el R ht
      rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, bor4_iff,
        tb_beq_iff (tb_cmpT ty tx) (tb_cmpT tx ty), tb_beq_iff (tb_cmpT ty tx) (tb_cmpT t2 ty),
        tb_beq_iff (tb_cmpT ty tx) (tb_cmpT t3 ty), tb_beq_iff (tb_cmpT ty tx) (tb_cmpT t4 ty)]
      exact ⟨fun h => ⟨elt_mem R ht, h⟩, fun h => h.2⟩
  ·
    obtain ⟨s, hs, hsx⟩ := elt_cover R x.2
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← hsx] at hx
    obtain ⟨h3a, h1a⟩ := (orderOf_prime_iff R hs).1 hx
    have tx := tb_el R hs
    have hn : ∀ k : Fin 5, nrm K VP (el K s) k.val = true ↔
        (x : Equiv.Perm (Fin 16)) ∈ Subgroup.normalizer (V k : Set (Equiv.Perm (Fin 16))) :=
      fun k => by rw [nrm_iff F k.isLt tx, hsx, ← mem_normalizer_iff F k.isLt]
    have h := CFSG.KS.Raw.Orb.allN_iff.1 h3 s hs
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq, h1a, h3a,
      Bool.not_false, Bool.true_and, if_pos rfl, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.strictB_eq,
      CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
    obtain ⟨hcnt, hw⟩ := h
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hw
    obtain ⟨hy, hyi, hyc, hk5, hl5, hkl, hnk, hnl, hcj⟩ := hw
    have hy60 := Nat.blt_eq.mp hy
    have hk5' := Nat.blt_eq.mp hk5
    have hl5' := Nat.blt_eq.mp hl5
    refine ⟨?_, ⟨elt R _, elt_mem R hy60⟩, (isInvT_iff R hy60).1 hyi, ?_,
      ⟨_, hk5'⟩, ⟨_, hl5'⟩, fun e => ?_, (hn ⟨_, hk5'⟩).1 hnk, (hn ⟨_, hl5'⟩).1 hnl, ?_⟩
    · rw [card_fin5 _ _ hn]
      exact Nat.eq_of_beq_eq_true hcnt
    · have ty := tb_el R hy60
      rw [CFSG.KS.Raw.Orb.strictB_eq, bor2_iff, tb_beq_iff (tb_cmpT ty tx) (tb_cmpT tx ty),
        tb_beq_iff (tb_cmpT ty tx) (tb_cmpT (tb_cmpT tx tx) ty)] at hyc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_pow, ← hsx, conj_iff, pow_two]
      exact hyc
    · have e' := congrArg Fin.val e
      simp only at e'
      rw [e', Nat.beq_refl] at hkl
      exact Bool.noConfusion hkl
    · exact map_eq_of F hk5' hl5' ((cnj_iff F hk5' hl5' (tb_el R hy60)).1 hcj)
  ·
    have h := Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 hN k.val k.isLt)
    rw [← h]
    exact card_states R _ _ (fun _ hx => (Subgroup.mem_inf.1 hx).2) (fun t ht => by
      rw [Subgroup.mem_inf, nrm_iff F k.isLt (tb_el R ht), ← mem_normalizer_iff F k.isLt]
      exact ⟨fun h => ⟨h, elt_mem R ht⟩, fun h => h.1⟩)

end F11

theorem rec0 : Rec (X16 0) SuzBtX0.K := by
  refine rec_of (i := 0) (fun j hj x => ?_) (by decide +kernel) kX0Cnt kX0Hd (fun s hs =>
    btSl_spec kX0Sl (Nat.zero_le _) (by rw [kX0Cnt] at hs; omega) hs)
  interval_cases j
  · rw [gpX_zero, tabPerm16, permC_val inj_xA]
    revert x
    decide +kernel
  · rw [gpX_one, tabPerm16, permC_val (inj_xB (by norm_num))]
    revert x
    decide +kernel

theorem rec1 : Rec (X16 1) SuzBtX1.K := by
  refine rec_of (i := 1) (fun j hj x => ?_) (by decide +kernel) kX1Cnt kX1Hd (fun s hs =>
    btSl_spec kX1Sl (Nat.zero_le _) (by rw [kX1Cnt] at hs; omega) hs)
  interval_cases j
  · rw [gpX_zero, tabPerm16, permC_val inj_xA]
    revert x
    decide +kernel
  · rw [gpX_one, tabPerm16, permC_val (inj_xB (by norm_num))]
    revert x
    decide +kernel

theorem rec2 : Rec (X16 2) SuzBtX2.K := by
  refine rec_of (i := 2) (fun j hj x => ?_) (by decide +kernel) kX2Cnt kX2Hd (fun s hs =>
    btSl_spec kX2Sl (Nat.zero_le _) (by rw [kX2Cnt] at hs; omega) hs)
  interval_cases j
  · rw [gpX_zero, tabPerm16, permC_val inj_xA]
    revert x
    decide +kernel
  · rw [gpX_one, tabPerm16, permC_val (inj_xB (by norm_num))]
    revert x
    decide +kernel

theorem rec3 : Rec (X16 3) SuzBtX3.K := by
  refine rec_of (i := 3) (fun j hj x => ?_) (by decide +kernel) kX3Cnt kX3Hd (fun s hs =>
    btSl_spec kX3Sl (Nat.zero_le _) (by rw [kX3Cnt] at hs; omega) hs)
  interval_cases j
  · rw [gpX_zero, tabPerm16, permC_val inj_xA]
    revert x
    decide +kernel
  · rw [gpX_one, tabPerm16, permC_val (inj_xB (by norm_num))]
    revert x
    decide +kernel

theorem f9Part1 : ∀ i < 4,
    Nat.card (X16 i) = 60 ∧ Tbar16 ≤ X16 i ∧
      ∀ x ∈ X16 i, (orderOf x = 3 ∨ orderOf x = 5) → ∀ j : Fin 16, x j = j → j = 0 := by
  intro i hi
  interval_cases i
  · exact part1 rec0 kX0Tb kX0Fx
  · exact part1 rec1 kX1Tb kX1Fx
  · exact part1 rec2 kX2Tb kX2Fx
  · exact part1 rec3 kX3Tb kX3Fx

theorem f11Prop : F11Prop := by
  intro i hi
  interval_cases i
  · exact f11_of rec0 kX0I kX0V kX0C kX05 kX03 kX0N
  · exact f11_of rec1 kX1I kX1V kX1C kX15 kX13 kX1N
  · exact f11_of rec2 kX2I kX2V kX2C kX25 kX23 kX2N
  · exact f11_of rec3 kX3I kX3V kX3C kX35 kX33 kX3N


end CertificateChecks.KernelSpor.SuzBtXG

end
