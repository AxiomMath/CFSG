module

public import Certificates.Kernel.LocalComp.J2End.Data
public import Certificates.Kernel.J2Cover.AutChain
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.HeFixKFix
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2EndTests
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.J2End

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.RankTwoSporadic.J2 CertificateChecks.KernelJ2Cover
open CFSG.ComponentClassification.J2Cover.Models

macro "pack_rw" : tactic => `(tactic| repeat (first
  | rw [invCand_unpack (by quickRfl)]
  | rw [compA_unpack (by quickRfl) (by quickRfl)]
  | rw [eqA_unpack (by quickRfl) (by quickRfl)]
  | rw [validA_unpack (by quickRfl)]))

@[expose] noncomputable def inPK (P : Nat) : Bool :=
  bAnd(canonK 315 9 (mask 9) (315 * 9) P,
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 P)

theorem inPK_sound {P : Nat} (h : inPK P = true) : j2InP (unpack 315 9 P) = true := by
  unfold inPK at h
  obtain ⟨hc, hs⟩ := (bAnd_iff _ _).1 h
  have hc' := hc
  simp only [canonK, bAnd_iff] at hc'
  exact inP_of rfl hc'.2.1 (range_of_canonK hc) hs

theorem countFold_countP (f : Nat → Bool) : ∀ n, countFold n f = (List.range n).countP f
  | 0 => by rw [countFold, Nat.fold_zero]; rfl
  | n + 1 => by
    have hs : countFold (n + 1) f = if f n then countFold n f + 1 else countFold n f := by
      rw [countFold, countFold, Nat.fold_succ]
    rw [hs, countFold_countP f n, List.range_succ, List.countP_append, List.countP_singleton]
    by_cases h : f n = true <;> simp [h]

theorem fixCount_unpack (p : Nat) : fixCountArr (unpack 315 9 p) = CFSG.KC.HeFixK.fixK 315 9 p := by
  rw [fixCountArr, countFold_countP, CFSG.KC.HeFixK.countP_fix]

theorem kId : idK 315 9 (mask 9) = true := by quickRfl
theorem kPid : canonK 315 9 (mask 9) (315 * 9) (pidn 315 9) = true := by quickRfl
theorem hid : idA 315 = unpack 315 9 (pidn 315 9) := (idK_sound kId).symm

@[expose] noncomputable def A0P : Nat := pkA 9 j2EndA0
@[expose] noncomputable def C0P : Nat := pkA 9 j2EndC0
@[expose] noncomputable def AP : Nat := pkA 9 CFSG.ComponentClassification.J2Cover.autStrong[0]!
@[expose] noncomputable def SP (i : Nat) : Nat :=
  pkA 9 CFSG.ComponentClassification.J2Cover.cent2BStrong[i]!
@[expose] noncomputable def XP (i : Nat) : Nat := pkA 9 j2EndLeaves[i]!

theorem hA0 : j2EndA0 = unpack 315 9 A0P := eq_unpack_of_bindListK (by quickRfl)
theorem hC0 : j2EndC0 = unpack 315 9 C0P := eq_unpack_of_bindListK (by quickRfl)
theorem hA : CFSG.ComponentClassification.J2Cover.autStrong[0]! = unpack 315 9 AP :=
  eq_unpack_of_bindListK (by quickRfl)
theorem hS0 : CFSG.ComponentClassification.J2Cover.cent2BStrong[0]! = unpack 315 9 (SP 0) :=
  eq_unpack_of_bindListK (by quickRfl)
theorem hS1 : CFSG.ComponentClassification.J2Cover.cent2BStrong[1]! = unpack 315 9 (SP 1) :=
  eq_unpack_of_bindListK (by quickRfl)

theorem kX : allN 8 (fun k => bindListK 315 9 (XP k) j2EndLeaves[k]!.toList) = true := by quickRfl
theorem hX (k : Nat) (hk : k < 8) : j2EndLeaves[k]! = unpack 315 9 (XP k) :=
  eq_unpack_of_bindListK (allN_spec kX k hk)

theorem kbE0 : allN E0.ng (fun k => bindListK 315 9 (E0.G k) j2E0[k]!.toList) = true := by quickRfl
theorem bE0 : j2E0.size = E0.ng ∧ ∀ k < E0.ng, j2E0[k]! = unpack 315 9 (E0.G k) :=
  binds_of_listK rfl kbE0
theorem pE0 : allN E0.ng (fun k => permOK 315 9 (mask 9) (315 * 9) (E0.G k)
    (pinvS 315 9 (mask 9) (E0.G k))) = true := by quickRfl
theorem keyE0 : keysK 315 9 j2PS E0.N E0.T = true := by quickRfl
theorem hE0 (k : Nat) (hk : k < 2) : j2E0[k]! = unpack 315 9 (E0.G k) := bE0.2 k hk

theorem kbN : allN N.ng (fun k => bindListK 315 9 (N.G k) j2EndN0[k]!.toList) = true := by
  quickRfl
theorem bN : j2EndN0.size = N.ng ∧ ∀ k < N.ng, j2EndN0[k]! = unpack 315 9 (N.G k) :=
  binds_of_listK rfl kbN
theorem pN : allN N.ng (fun k => permOK 315 9 (mask 9) (315 * 9) (N.G k)
    (pinvS 315 9 (mask 9) (N.G k))) = true := by quickRfl
theorem keyN : keysK 315 9 j2PS N.N N.T = true := by quickRfl
theorem hN (k : Nat) (hk : k < 2) : j2EndN0[k]! = unpack 315 9 (N.G k) := bN.2 k hk

theorem setE0 : enumOK 315 j2E0 j2PS (enumBfs 315 j2E0 j2PS j2Fuel) = true ∧
    (∀ x, x ∈ (enumBfs 315 j2E0 j2PS j2Fuel).pts ↔ ∃ i < E0.N, unpack 315 9 (E0.T i) = x) ∧
    (enumBfs 315 j2E0 j2PS j2Fuel).pts.size = E0.N :=
  enumBfs_of_bfsK_set bE0.1 bE0.2
    (fun k hk => allN_spec pE0 k hk) kId kPid E0.ok j2PS_lt keyE0 (by decide)

theorem setN : enumOK 315 j2EndN0 j2PS (enumBfs 315 j2EndN0 j2PS j2Fuel) = true ∧
    (∀ x, x ∈ (enumBfs 315 j2EndN0 j2PS j2Fuel).pts ↔ ∃ i < N.N, unpack 315 9 (N.T i) = x) ∧
    (enumBfs 315 j2EndN0 j2PS j2Fuel).pts.size = N.N :=
  enumBfs_of_bfsK_set bN.1 bN.2
    (fun k hk => allN_spec pN k hk) kId kPid N.ok j2PS_lt keyN (by decide)

theorem e0size : j2E0.size = 2 := rfl
theorem nsize : j2EndN0.size = 2 := rfl
theorem xsize : j2EndLeaves.size = 8 := rfl

theorem kE0in : allN 2 (fun k => inPK (E0.G k)) = true := by quickRfl

theorem kE0fix : allN E0.N (fun i => Nat.beq (E0.T i) (pidn 315 9) ||
    CFSG.KC.HeFixK.fixK 315 9 (E0.T i) == 15) = true := by quickRfl

theorem e0OK : j2EndE0OK j2E0 = true := by
  obtain ⟨hok, hmem, -⟩ := setE0
  unfold j2EndE0OK
  simp only [Bool.and_eq_true]
  refine ⟨⟨hok, allLt_iff.2 fun i hi => ?_⟩, ?_⟩
  · rw [e0size] at hi
    rw [hE0 i hi]
    exact inPK_sound (allN_spec kE0in i hi)
  · refine allLt_pts (f := fun x => eqA 315 x (idA 315) || fixCountArr x == 15) hmem
      (fun i hi => ?_)
    have hc := bfsK_canon E0.ok i hi
    simp only [hid, eqA_unpack hc kPid, fixCount_unpack]
    exact allN_spec kE0fix i hi

theorem commA_unpack {p q : Nat} (hp : canonK 315 9 (mask 9) (315 * 9) p = true)
    (hq : canonK 315 9 (mask 9) (315 * 9) q = true) :
    CFSG.ComponentClassification.RankTwoSporadic.J2.commA (unpack 315 9 p) (unpack 315 9 q) =
      Nat.beq (pcomp 315 9 (mask 9) p q) (pcomp 315 9 (mask 9) q p) := by
  unfold CFSG.ComponentClassification.RankTwoSporadic.J2.commA
  rw [compA_unpack hp hq, compA_unpack hq hp, eqA_unpack (canonK_pcomp hp hq) (canonK_pcomp hq hp)]

theorem kX0 : allN 8 (fun k => bAnd(inPK (XP k), permOK 315 9 (mask 9) (315 * 9) (XP k)
    (pinvS 315 9 (mask 9) (XP k)))) = true := by quickRfl

theorem kXc : allN 8 (fun k => allN 2 fun j => Nat.beq (pcomp 315 9 (mask 9) (XP k) (E0.G j))
    (pcomp 315 9 (mask 9) (E0.G j) (XP k))) = true := by quickRfl

theorem kXcan : allN 8 (fun k => canonK 315 9 (mask 9) (315 * 9) (XP k)) = true := by quickRfl
theorem kE0can : allN 2 (fun k => canonK 315 9 (mask 9) (315 * 9) (E0.G k)) = true := by quickRfl

theorem treeK : treeOK j2EndLeaves (compA 315 j2E0[0]! (conjInvA 315 j2EndA0 j2E0[0]!)) = true := by
  unfold treeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨xsize, allLt_iff.2 fun i hi => ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hX i hi]
    exact validA_unpack ((bAnd_iff _ _).1 (allN_spec kX0 i hi)).2
  all_goals
    simp only [hX 0 (by decide), hX 1 (by decide), hX 2 (by decide), hX 3 (by decide),
      hX 4 (by decide), hX 5 (by decide), hX 6 (by decide), hX 7 (by decide), hE0 0 (by decide),
      hA0, commutatorA, conjInvA]
    pack_rw
  all_goals quickRfl

theorem conjOK : j2EndConjOK j2E0 j2EndA0 j2EndC0 j2EndLeaves = true := by
  obtain ⟨-, hmem, -⟩ := setE0
  unfold j2EndConjOK
  simp only [Bool.and_eq_true, inEnum, any_pts hmem]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_, treeK⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hA0]
    exact validA_unpack (by quickRfl)
  · rw [hA0]
    exact inPK_sound (by quickRfl)
  · refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
    rw [e0size] at hi hj
    interval_cases i <;> interval_cases j <;>
      simp only [hE0 0 (by decide), hE0 1 (by decide), hA0, conjInvA,
        CFSG.ComponentClassification.RankTwoSporadic.J2.commA] <;> pack_rw <;> quickRfl
  · simp only [hE0 0 (by decide), hA0, conjInvA]
    pack_rw
    rw [any_eqA_unpack_range (by quickRfl) (bfsK_canon E0.ok)]
    quickRfl
  · refine allLt_iff.2 fun i hi => ?_
    rw [xsize] at hi
    rw [hX i hi, Bool.and_eq_true]
    refine ⟨inPK_sound ((bAnd_iff _ _).1 (allN_spec kX0 i hi)).1, allLt_iff.2 fun j hj => ?_⟩
    rw [e0size] at hj
    rw [hE0 j hj, commA_unpack (allN_spec kXcan i hi) (allN_spec kE0can j hj)]
    exact allN_spec (allN_spec kXc i hi) j hj
  · rw [hC0]
    exact validA_unpack (by quickRfl)
  · rw [hC0]
    exact inPK_sound (by quickRfl)
  · simp only [hE0 0 (by decide), hC0, hA, conjA]
    pack_rw
    quickRfl

theorem kNinv : allN N.N (fun i =>
    !Nat.beq (pcomp 315 9 (mask 9) (N.T i) (N.T i)) (pidn 315 9) ||
      Nat.beq (N.T i) (pidn 315 9) || CFSG.KC.HeFixK.fixK 315 9 (N.T i) != 15) = true := by
  quickRfl

theorem derOK : j2EndDerOK j2EndN0 = true := by
  obtain ⟨hok, hmem, -⟩ := setN
  have hT := bfsK_canon N.ok
  unfold j2EndDerOK
  simp only [Bool.and_eq_true, inEnum, any_pts hmem]
  refine ⟨⟨⟨⟨⟨hok, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hS0]
    exact validA_unpack (by quickRfl)
  · rw [hS1]
    exact validA_unpack (by quickRfl)
  · refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
    rw [nsize] at hj
    interval_cases i <;> interval_cases j <;>
      simp only [Bool.and_eq_true, hN 0 (by decide), hN 1 (by decide), hS0, hS1, conjA,
        conjInvA] <;> pack_rw <;>
      refine ⟨?_, ?_⟩ <;> rw [any_eqA_unpack_range (by quickRfl) hT] <;> quickRfl
  · simp only [hS0, hS1, commutatorA]
    pack_rw
    rw [any_eqA_unpack_range (by quickRfl) hT]
    quickRfl
  · refine allLt_pts (f := fun x => !eqA 315 (compA 315 x x) (idA 315) || eqA 315 x (idA 315) ||
      fixCountArr x != 15) hmem (fun i hi => ?_)
    have hc := hT i hi
    simp only [hid, compA_unpack hc hc, eqA_unpack (canonK_pcomp hc hc) kPid, eqA_unpack hc kPid,
      fixCount_unpack]
    exact allN_spec kNinv i hi

theorem j2EndCheck_eq_true : j2EndCheck j2E0 j2EndA0 j2EndC0 j2EndLeaves j2EndN0 = true := by
  unfold j2EndCheck
  simp only [e0OK, conjOK, derOK, Bool.and_self]

end CertificateChecks.KernelLC.J2End

end
