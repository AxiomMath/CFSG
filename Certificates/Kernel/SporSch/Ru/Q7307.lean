
module

public import CFSG.Quasithin.Recognition.RuRank3J55DataInputs
public import Certificates.Kernel.SporSch.Ru.Q7307K
import Certificates.Kernel.SporSch.Ru.Iso7047
import Certificates.Kernel.SporSch.Ru.G2Ru7164
import Certificates.Kernel.SporSch.Tits.Graph2265N
import CFSG.Certificates.Kernel.SporSch.OrbLabelsSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Q7307

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.KC.BfsPin

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem nat_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem qlab_get {y : Nat} (hy : y < 4060) : ruQLab[y]! = Lf y := by
  have hs : ruR0Arrs.size = 4 := by simp [ruR0Arrs]
  have hg : ∀ k < 4, ∀ x < 4060, ga ruR0Arrs k x = gR k x := fun k hk x hx => by
    unfold ga ruR0Arrs
    rw [getElem!_ofFn_of_lt _ hk]
    change (ruR0Arr k)[x]! = _
    rw [Iso7047.r_eq hk, CFSG.KC.BfsPin.unpack_get' hx]
    rfl
  exact (orbLabels_of_K hs hg kOrb).2 y hy

theorem ti_eq : ruTI1 = unpack 4060 12 TI := by
  have hP : ∀ j < 2, P (Af j) := fun j hj => by
    interval_cases j
    · exact PP_of_permOK hsz kPerm0
    · exact PP_of_permOK hsz kPerm1
  have hS : ∀ j < 2, ruGensA[j]! = unpack 4060 12 (Af j) := fun j hj => by
    interval_cases j
    · rw [show ruGensA[0]! = ruA0A by simp [ruGensA], a0_eq]
      rfl
    · rw [show ruGensA[1]! = ruA1A by simp [ruGensA], a1_eq]
      rfl
  have hinv : ruGensInvA = ruGensA.map (invCand 4060) := by
    simp [ruGensInvA, ruGensA, ruInv]
  have hw : ∀ l ∈ Iso7047.twK 32 1, l ≠ 0 ∧ l.natAbs ≤ 2 := fun l hl => by
    have := List.all_eq_true.1 kWord l hl
    simpa using this
  have e : ruTreeWord 1 = Iso7047.twK 32 1 := Iso7047.treeWordAux_eq 32 1 (by norm_num)
  obtain ⟨h1, h2⟩ := wordA_eq (S := ruGensA) (k := 2) (by simp [ruGensA]) hS hP _ hw
  change invCand 4060 (wordA 4060 ruGensA ruGensInvA (ruTreeWord 1)) = _
  rw [hinv, e, h1, inv_eq h2]
  rfl

theorem testBit_maskL : ∀ (l : List Nat) (x : Nat), (maskL l).testBit x = decide (x ∈ l)
  | [], x => by simp [maskL]
  | y :: l, x => by
    have e : maskL (y :: l) = (1 <<< y) ||| maskL l := rfl
    rw [e, Nat.testBit_or, testBit_maskL l x, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : y = x
    · subst h
      simp
    · simp [h, List.mem_cons, Ne.symm h]

theorem step_eq {L : List Nat} (hL : ∀ x ∈ L, x < 1755) :
    titsStepL L = stepK L ∧ ∀ x ∈ stepK L, x < 1755 := by
  have hrow : ∀ x ∈ L, (titsNbr[x]!).toList =
      (List.range 10).map fun i => pgW 11 TitsGN.NB (10 * x + i) := fun x hx => by
    rw [CertificateChecks.KernelSporSch.TitsGraph.nbr_get (hL x hx)]
    rw [Array.toList_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  refine ⟨?_, fun y hy => ?_⟩
  · unfold titsStepL stepK
    congr 1
    exact List.flatMap_congr hrow
  · unfold stepK at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hL y hy
    · obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.1 hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hyx
      have := allN_spec (allN_spec kNbr x (hL x hx)) i (List.mem_range.1 hi)
      simpa using this

theorem ball_eq : titsBallL3 = ballK := by
  have h0 : ∀ x ∈ [0], x < 1755 := by simp
  obtain ⟨e1, b1⟩ := step_eq h0
  obtain ⟨e2, b2⟩ := step_eq b1
  obtain ⟨e3, -⟩ := step_eq b2
  unfold titsBallL3 ballK
  rw [e1, e2, e3]

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem c7307 :
    (allLt 1755 fun j => titsBallArr[j]! == (j == 0 || ruRowA ruTI1 ruDArr[j]!)) = true := by
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => ?_
  have h := kMain
  rw [strictB_eq, strictB_eq] at h
  have hp := allN_spec h j hj
  unfold ptOK at hp
  obtain ⟨hlt, heq⟩ := (bAnd_iff _ _).1 hp
  obtain ⟨dj, djl, -⟩ := Iso7047.d_get hj
  have hball : titsBallArr[j]! = (maskL ballK).testBit j := by
    unfold titsBallArr
    rw [getElem!_ofFn_of_lt _ hj, testBit_maskL, ← ball_eq]
    simp [List.contains_iff_mem]
  have hrow : ruRowA ruTI1 ruDArr[j]! = Nat.beq (Lf (fl TI (fl Iso7047.D j))) (Lf 1) := by
    unfold ruRowA
    rw [dj, ti_eq, CFSG.KC.BfsPin.unpack_get' djl, qlab_get (by unfold fl at hlt; simpa using hlt),
      qlab_get (by norm_num), nat_beq]
    rfl
  rw [hball, hrow, nat_beq]
  exact heq

end CertificateChecks.KernelSporSch.Q7307

end
