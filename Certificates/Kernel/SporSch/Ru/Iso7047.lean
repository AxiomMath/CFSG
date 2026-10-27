
module

public import Certificates.Kernel.SporSch.Ru.Iso7047K
import Certificates.Kernel.SporSch.Ru.JFacts
import Certificates.Kernel.Sporadic.Tits.Bind2264
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Iso7047

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSporSch.RuG
  CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Schreier.Tits

theorem r_eq {i : Nat} (hi : i < 4) : ruR0Arr i = unpack 4060 12 (R i) := by
  rw [ruR0Arr, Iso7047R.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound Iso7047R.all i hi

theorem d_eq : ruDArr = unpack 1755 12 D := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Iso7047D.all 0 (by norm_num)
  rw [Nat.mul_zero] at h
  rw [ruDArr, Iso7047D.eq]
  exact h

theorem par_eq : ruTreePar = unpack 4060 12 Par := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Iso7047P.all 0 (by norm_num)
  rw [Nat.mul_zero] at h
  rw [ruTreePar, Iso7047P.eq]
  exact h

theorem lab_eq : ruTreeLab = unpack 4060 4 Lab := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Iso7047L.all 0 (by norm_num)
  rw [Nat.mul_zero] at h
  rw [ruTreeLab, Iso7047L.eq]
  exact h

theorem range_of {i : Nat} (hi : i < 4060) :
    pg 12 (mask 12) A0 i < 4060 ∧ pg 12 (mask 12) A1 i < 4060 ∧ pg 12 (mask 12) A0I i < 4060 ∧
      pg 12 (mask 12) A1I i < 4060 ∧ pg 12 (mask 12) Par i < 4060 := by
  have h := allN_spec kRange i hi
  simp only [bAnd_iff, Nat.blt_eq] at h
  exact h

theorem perm_A : pk A0 A0I = true ∧ pk A1 A1I = true := by
  have h := kPerm
  simp only [bAnd_iff] at h
  exact h

theorem compA_get {n : Nat} {t u : Array Nat} {i : Nat} (hi : i < n) :
    (compA n t u)[i]! = t[u[i]!]! := by
  unfold compA
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

@[expose] def GoodL (l : Int) : Prop := l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2

private theorem lp1 (a b c d : Array Nat) : letterA #[a, b] #[c, d] 1 = a := rfl
private theorem lp2 (a b c d : Array Nat) : letterA #[a, b] #[c, d] 2 = b := rfl
private theorem lm1 (a b c d : Array Nat) : letterA #[a, b] #[c, d] (-1) = c := rfl
private theorem lm2 (a b c d : Array Nat) : letterA #[a, b] #[c, d] (-2) = d := rfl

theorem letter_eq {l : Int} (hl : GoodL l) :
    letterA ruGensA ruGensInvA l = unpack 4060 12 (gK l) ∧
      ∀ p < 4060, pg 12 (mask 12) (gK l) p < 4060 := by
  rcases hl with rfl | rfl | rfl | rfl
  · refine ⟨?_, fun p hp => (range_of hp).1⟩
    have e1 : letterA ruGensA ruGensInvA 1 = ruA0A := by
      rw [ruGensA, ruGensInvA]; exact lp1 _ _ _ _
    have e2 : gK 1 = A0 := rfl
    rw [e1, e2, a0_eq]
  · refine ⟨?_, fun p hp => (range_of hp).2.1⟩
    have e1 : letterA ruGensA ruGensInvA 2 = ruA1A := by
      rw [ruGensA, ruGensInvA]; exact lp2 _ _ _ _
    have e2 : gK 2 = A1 := rfl
    rw [e1, e2, a1_eq]
  · refine ⟨?_, fun p hp => (range_of hp).2.2.1⟩
    have e1 : letterA ruGensA ruGensInvA (-1) = ruInv ruA0A := by
      rw [ruGensA, ruGensInvA]; exact lm1 _ _ _ _
    have e2 : gK (-1) = A0I := rfl
    rw [e1, e2]
    exact (inv_of a0_eq perm_A.1).1
  · refine ⟨?_, fun p hp => (range_of hp).2.2.2.1⟩
    have e1 : letterA ruGensA ruGensInvA (-2) = ruInv ruA1A := by
      rw [ruGensA, ruGensInvA]; exact lm2 _ _ _ _
    have e2 : gK (-2) = A1I := rfl
    rw [e1, e2]
    exact (inv_of a1_eq perm_A.2).1

theorem wordA_zero : ∀ w : List Int, (∀ l ∈ w, GoodL l) →
    (wordA 4060 ruGensA ruGensInvA w)[0]! = ptK w ∧ ptK w < 4060
  | [], _ => by
    refine ⟨?_, by decide⟩
    unfold wordA idA
    rw [getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
    rfl
  | l :: w, h => by
    obtain ⟨ih1, ih2⟩ := wordA_zero w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨e, hr⟩ := letter_eq (h l List.mem_cons_self)
    have e2 : ptK (l :: w) = pg 12 (mask 12) (gK l) (ptK w) := rfl
    have e3 : wordA 4060 ruGensA ruGensInvA (l :: w) =
        compA 4060 (letterA ruGensA ruGensInvA l) (wordA 4060 ruGensA ruGensInvA w) := rfl
    rw [e3, compA_get (by norm_num), ih1, e, CFSG.KC.BfsPin.unpack_get' ih2, e2]
    exact ⟨rfl, hr _ ih2⟩

theorem treeWordAux_eq : ∀ f x, x < 4060 → ruTreeWordAux f x = twK f x
  | 0, _, _ => rfl
  | f + 1, x, hx => by
    by_cases h0 : x = 0
    · subst h0
      rfl
    · have e1 : ruTreeWordAux (f + 1) x =
          ruTreeLetter ruTreeLab[x]! :: ruTreeWordAux f ruTreePar[x]! := by
        simp [ruTreeWordAux, h0]
      have hb : Nat.beq x 0 = false := by
        cases h : Nat.beq x 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h0
      have e2' : twK (f + 1) x = Bool.rec (motive := fun _ => List Int)
          (List.cons (ruTreeLetter (pg 4 (mask 4) Lab x)) (twK f (pg 12 (mask 12) Par x))) []
          (Nat.beq x 0) := rfl
      have e2 : twK (f + 1) x =
          ruTreeLetter (pg 4 (mask 4) Lab x) :: twK f (pg 12 (mask 12) Par x) := by
        rw [e2', hb]
      have hp := (range_of hx).2.2.2.2
      rw [e1, e2, lab_eq, par_eq, CFSG.KC.BfsPin.unpack_get' hx, CFSG.KC.BfsPin.unpack_get' hx,
        treeWordAux_eq f _ hp]

theorem good_of {w : List Int} (h : lettersOK 2 w = true) : ∀ l ∈ w, GoodL l := by
  intro l hl
  unfold lettersOK at h
  have := List.all_eq_true.1 h l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  unfold GoodL
  omega

theorem tree_ok : (allLt 4060 fun x => lettersOK 2 (ruTreeWord x) && (ruTreeArr x)[0]! == x) =
    true := by
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro x hx
  have h := allN_spec kTree x hx
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have ew : ruTreeWord x = twK 32 x := treeWordAux_eq 32 x hx
  rw [Bool.and_eq_true, ruTreeArr, ew, (wordA_zero _ (good_of h1)).1, Nat.eq_of_beq_eq_true h2]
  exact ⟨h1, beq_self_eq_true x⟩

theorem d_get {j : Nat} (hj : j < 1755) :
    ruDArr[j]! = pg 12 (mask 12) D j ∧ pg 12 (mask 12) D j < 4060 ∧ pg 12 (mask 12) D j ≠ 0 := by
  have h := kD
  simp only [bAnd_iff] at h
  have h2 := allN_spec h.2 j hj
  simp only [bAnd_iff, Nat.blt_eq] at h2
  refine ⟨by rw [d_eq, CFSG.KC.BfsPin.unpack_get' hj], h2.1, fun h0 => ?_⟩
  have := h2.2
  rw [h0] at this
  exact absurd this (by decide)

theorem r_ok {i : Nat} (hi : i < 4) :
    (isInvA 4060 (ruR0Arr i) (invCand 4060 (ruR0Arr i)) &&
      ruSift 4060 (ruField4060 3) ruJoinBase (ruR0Arr i) && (ruR0Arr i)[0]! == 0 &&
      allLt 1755 fun j => (ruR0Arr i)[ruDArr[j]!]! == ruDArr[(titsGenArrs[i]!)[j]!]!) = true := by
  have h : rOK i = true := by
    interval_cases i
    exacts [kR0, kR1, kR2, kR3]
  unfold rOK at h
  simp only [bAnd_iff] at h
  obtain ⟨hperm, hhi, hrange, hsift, h0, hmap⟩ := h
  have hR := r_eq hi
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨(inv_of hR hperm).2, ?_⟩, ?_⟩, ?_⟩
  · exact siftK_soundR RuJ.bindsJ RuJ.permJ RuJS.hl hR (Nat.eq_of_beq_eq_true hhi) hrange hsift
  · rw [hR, CFSG.KC.BfsPin.unpack_get' (by norm_num)]
    exact Nat.eq_of_beq_eq_true h0
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have hm := allN_spec hmap j hj
    simp only [bAnd_iff, Nat.blt_eq] at hm
    obtain ⟨hT, hE⟩ := hm
    obtain ⟨dj, djl, -⟩ := d_get hj
    obtain ⟨dt, -, -⟩ := d_get hT
    rw [CertificateChecks.KernelSpor.Tits2264.gen_eq hi, CFSG.KC.BfsPin.unpack_get' hj, dj, dt, hR,
      CFSG.KC.BfsPin.unpack_get' djl, Nat.eq_of_beq_eq_true hE]
    exact beq_self_eq_true _

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem c7047 :
    (allLt 4060 fun x => lettersOK 2 (ruTreeWord x) && (ruTreeArr x)[0]! == x) = true ∧
      (allLt 4 fun i => isInvA 4060 (ruR0Arr i) (invCand 4060 (ruR0Arr i)) &&
        ruSift 4060 (ruField4060 3) ruJoinBase (ruR0Arr i) && (ruR0Arr i)[0]! == 0 &&
        allLt 1755 fun j => (ruR0Arr i)[ruDArr[j]!]! == ruDArr[(titsGenArrs[i]!)[j]!]!) = true ∧
      (allLt 1755 fun j => decide (ruDArr[j]! < 4060) && ruDArr[j]! != 0) = true ∧
      (allLt 1755 fun j => allLt j fun j' => ruDArr[j]! != ruDArr[j']!) = true ∧
      ruDArr[0]! = 1 := by
  refine ⟨tree_ok, ?_, ?_, ?_, (d_get (by norm_num)).1.trans ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    exact r_ok hi
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    obtain ⟨e, hl, hne⟩ := d_get hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, e]
    exact ⟨hl, hne⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j' hj'
    obtain ⟨e, -, -⟩ := d_get hj
    obtain ⟨e', -, -⟩ := d_get (show j' < 1755 by omega)
    rw [e, e', bne_iff_ne, ne_eq]
    intro hEq
    have q1 := Nat.eq_of_beq_eq_true (allN_spec kDist j hj)
    have q2 := Nat.eq_of_beq_eq_true (allN_spec kDist j' (by omega))
    rw [hEq] at q1
    omega
  · have h := kD
    simp only [bAnd_iff] at h
    exact Nat.eq_of_beq_eq_true h.1

end CertificateChecks.KernelSporSch.Iso7047

end
