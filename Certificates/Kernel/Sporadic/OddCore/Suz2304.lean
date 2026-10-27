
module

public import Certificates.Kernel.Sporadic.OddCore.SuzCert
public import Certificates.Kernel.Sporadic.OddCore.SuzOuter
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.Spor.RowWordSound
public import CFSG.Sporadic.SuzOddCore.OuterCheckInputs
public import CFSG.Sporadic.SuzOddCore.CertChainCheckInputs
import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Sporadic.SuzOddCore.GraphArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Row

@[expose] noncomputable def ocs (h : Nat) : Nat := Nat.mul 715 (Nat.add h 2)

@[expose] noncomputable def cg (k x : Nat) : Nat := rg 15 (mask 15) SuzCertT.F (Nat.mul 715 k) x

@[expose] noncomputable def og (x : Nat) : Nat := rg 15 (mask 15) SuzOutT.F 0 x

@[expose] noncomputable def wpt (wd : List Int) (x : Nat) : Nat :=
  rwordPt 15 (mask 15) SuzCertT.F SuzCertI ocs wd x

@[expose] def strip0 : List Int := [9, 9, 2, 4, 3, 1, 5, 5, 4, 7, 9, 4, 7, 8, 8, 5, 10]

@[expose] def strip1 : List Int := [8, 2, 10, 4, 4, 2, 10, 3, 4, 6, 7, 4, 6, 9, 5, 6, 5, 10]

@[expose] noncomputable def movesK (L : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun k _ ih => bIf(Nat.beq (cg k x) x, ih, true)) L

theorem k_rev : allN 12 (fun k =>
    rpermK 22880 15 (mask 15) SuzCertI (Nat.mul 715 k) SuzCertT.F (Nat.mul 715 k)) = true := by
  quickRfl

theorem k_oo : allN 22880 (fun x => Nat.beq (og (og x)) x) = true := by
  quickRfl

theorem k_pts : bAnd(bIf(Nat.beq (og 0) 0, false, true),
    bAnd(Nat.beq (wpt uRejectWord (og 0)) 0, bAnd(Nat.beq (wpt uRejectWord (og 1)) 1,
    bAnd(Nat.beq (wpt uRejectWord (og 2)) 2, bAnd(Nat.beq (wpt uRejectWord (og 3)) 2862,
    bAnd(Nat.beq (cg 11 (cg 11 3)) 3, bIf(Nat.beq (cg 11 3) 2862, false, true))))))) = true := by
  quickRfl

theorem k_strip0 : allN 22880 (fun x => Nat.beq (og (cg 0 (og x))) (wpt strip0 x)) = true := by
  quickRfl

theorem k_strip1 : allN 22880 (fun x => Nat.beq (og (cg 1 (og x))) (wpt strip1 x)) = true := by
  quickRfl

theorem k_stab : allN 22880 (fun x =>
    bIf(Nat.beq x 0, true, movesK [4, 5, 6, 7, 8, 9, 10, 11] x)) = true := by
  quickRfl

theorem movesK_spec : ∀ (L : List Nat) (x : Nat), movesK L x = true → ∃ k ∈ L, cg k x ≠ x
  | [], _, h => absurd h (by simp [movesK])
  | k :: L, x, h => by
    change Bool.rec (motive := fun _ => Bool) true (movesK L x) (Nat.beq (cg k x) x) = true at h
    cases hb : Nat.beq (cg k x) x
    · rw [hb] at h
      exact ⟨k, List.mem_cons_self, fun he => by simp [he] at hb⟩
    · rw [hb] at h
      obtain ⟨k', hk', hne⟩ := movesK_spec L x h
      exact ⟨k', List.mem_cons_of_mem k hk', hne⟩

theorem strong_get {j : Nat} (hj : j < 10) : certStrongArrs[j]! = certArr (j + 2) := by
  interval_cases j <;> simp [certStrongArrs]

theorem strong_rows {j : Nat} (hj : j < 10) :
    certStrongArrs[j]! = rowArr 22880 15 SuzCertT.F (ocs j) := by
  rw [strong_get hj, certArr_eq (by omega)]
  rfl

theorem strongInv_rows {j : Nat} (hj : j < 10) :
    certStrongInvs[j]! = rowArr 22880 15 SuzCertI (ocs j) := by
  have e : certStrongInvs[j]! = invCand 22880 certStrongArrs[j]! := by
    interval_cases j <;> simp [certStrongInvs, certStrongArrs]
  rw [e, strong_get hj, certArr_eq (by omega)]
  exact (rpermK_sound (allN_spec cert_perms (j + 2) (by omega))).1

theorem rangeF {j : Nat} (hj : j < 10) : ∀ i < 22880, rg 15 (mask 15) SuzCertT.F (ocs j) i < 22880 :=
  rpermK_range (allN_spec cert_perms (j + 2) (by omega))

theorem rangeG {j : Nat} (hj : j < 10) : ∀ i < 22880, rg 15 (mask 15) SuzCertI (ocs j) i < 22880 :=
  rpermK_range (allN_spec k_rev (j + 2) (by omega))

theorem word_get {wd : List Int} (hl : lettersOK 10 wd = true) {x : Nat} (hx : x < 22880) :
    (wordA 22880 certStrongArrs certStrongInvs wd)[x]! = wpt wd x :=
  (rwordPt_eq (fun _ hj => strong_rows hj) (fun _ hj => strongInv_rows hj)
    (fun _ hj => rangeF hj) (fun _ hj => rangeG hj) wd hl x hx).1

theorem outer_get {x : Nat} (hx : x < 22880) : outerArr[x]! = og x := by
  rw [outerArr_eq, rowArr_get hx]
  rfl

theorem outer_lt {x : Nat} (hx : x < 22880) : og x < 22880 :=
  rpermK_range outer_perm x hx

theorem cert_get {k x : Nat} (hk : k < 12) (hx : x < 22880) : (certArr k)[x]! = cg k x := by
  rw [certArr_eq hk, rowArr_get hx]
  rfl

theorem strip_eq {i : Nat} (hi : i < 12) {wd : List Int} (hwd : uStripWord i = wd)
    (hl : lettersOK 10 wd = true)
    (hk : ∀ x < 22880, Nat.beq (og (cg i (og x))) (wpt wd x) = true) :
    lettersOK 10 (uStripWord i) = true ∧
      eqA 22880 (compA 22880 outerArr (compA 22880 (certArr i) outerArr))
        (wordA 22880 certStrongArrs certStrongInvs (uStripWord i)) = true := by
  rw [hwd]
  refine ⟨hl, (eqA_iff _ _ _).2 fun x hx => ?_⟩
  have hy : cg i (og x) < 22880 := rpermK_range (allN_spec cert_perms i hi) _ (outer_lt hx)
  rw [compA_get hx, compA_get hx, outer_get hx, cert_get hi (outer_lt hx), outer_get hy,
    word_get hl hx]
  exact Nat.eq_of_beq_eq_true (hk x hx)

theorem uStrip0 : uStripWord 0 = strip0 := by decide

theorem uStrip1 : uStripWord 1 = strip1 := by decide

theorem facts2304 :
    eqA 22880 (compA 22880 outerArr outerArr) (idA 22880) = true ∧
    eqA 22880 outerArr (idA 22880) = false ∧
    lettersOK 10 uRejectWord = true ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[0]! = 0 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[1]! = 1 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[2]! = 2 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[3]! = 2862 ∧
    certStrongArrs[9]![certStrongArrs[9]![3]!]! = 3 ∧ certStrongArrs[9]![3]! ≠ 2862 ∧
    (∀ i < 2, lettersOK 10 (uStripWord i) = true ∧
      eqA 22880 (compA 22880 outerArr (compA 22880 (certArr i) outerArr))
        (wordA 22880 certStrongArrs certStrongInvs (uStripWord i)) = true) ∧
    (∀ x < 22880, x ≠ 0 → ∃ j ∈ certStabIdx, certStrongArrs[j]![x]! ≠ x) := by
  have hl : lettersOK 10 uRejectWord = true := by decide
  obtain ⟨p0, w0, w1, w2, w3, c1, c2⟩ := (by simpa only [bAnd_iff] using k_pts :
    bIf(Nat.beq (og 0) 0, false, true) = true ∧
    Nat.beq (wpt uRejectWord (og 0)) 0 = true ∧ Nat.beq (wpt uRejectWord (og 1)) 1 = true ∧
    Nat.beq (wpt uRejectWord (og 2)) 2 = true ∧ Nat.beq (wpt uRejectWord (og 3)) 2862 = true ∧
    Nat.beq (cg 11 (cg 11 3)) 3 = true ∧ bIf(Nat.beq (cg 11 3) 2862, false, true) = true)
  have pt : ∀ i < 22880,
      (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[i]! =
        wpt uRejectWord (og i) := fun i hi => by
    rw [compA_get hi, outer_get hi, word_get hl (outer_lt hi)]
  have s9 : ∀ x < 22880, certStrongArrs[9]![x]! = cg 11 x := fun x hx => by
    rw [strong_get (by omega), cert_get (by omega) hx]
  refine ⟨?_, ?_, hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eqA_iff]
    intro i hi
    rw [compA_get hi, outer_get hi, outer_get (outer_lt hi), idA_get hi]
    exact Nat.eq_of_beq_eq_true (allN_spec k_oo i hi)
  · refine eqA_false (i := 0) (by omega) ?_
    rw [outer_get (by omega), idA_get (by omega)]
    intro h
    rw [h] at p0
    exact absurd p0 (by decide)
  · rw [pt 0 (by omega)]
    exact Nat.eq_of_beq_eq_true w0
  · rw [pt 1 (by omega)]
    exact Nat.eq_of_beq_eq_true w1
  · rw [pt 2 (by omega)]
    exact Nat.eq_of_beq_eq_true w2
  · rw [pt 3 (by omega)]
    exact Nat.eq_of_beq_eq_true w3
  · have e3 := Nat.eq_of_beq_eq_true c1
    have hlt : cg 11 3 < 22880 := rpermK_range (allN_spec cert_perms 11 (by omega)) 3 (by omega)
    rw [s9 3 (by omega), s9 _ hlt]
    exact e3
  · rw [s9 3 (by omega)]
    intro h
    rw [h] at c2
    exact absurd c2 (by decide)
  · intro i hi
    interval_cases i
    · exact strip_eq (by omega) uStrip0 (by decide) (fun x hx => allN_spec k_strip0 x hx)
    · exact strip_eq (by omega) uStrip1 (by decide) (fun x hx => allN_spec k_strip1 x hx)
  · intro x hx hx0
    have h := allN_spec k_stab x hx
    have hb : Nat.beq x 0 = false := by
      cases hb : Nat.beq x 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hx0
    rw [hb] at h
    obtain ⟨k, hk, hne⟩ := movesK_spec _ x h
    refine ⟨k - 2, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      simp only [certStabIdx, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · have hk' : 4 ≤ k ∧ k ≤ 11 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        omega
      rw [strong_get (by omega), Nat.sub_add_cancel (by omega), cert_get (by omega) hx]
      exact hne

end CertificateChecks.KernelSpor.OddCore

end
