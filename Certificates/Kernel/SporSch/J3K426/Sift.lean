module

public import Certificates.Kernel.SporSch.J3K426.Glue
public import Certificates.Kernel.SporSch.PairJ3.Check2237

public section

namespace CertificateChecks.KernelSporSch.J3KT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ3 CFSG.RankThree.PartTwo.KFacts.K426

theorem hd : Hd 6156 j3StrongArrs baseArr 2 j3Words := by
  have h := PJ3Check.facts.1.1
  refine hd_of_head (by simp [j3StrongArrs]) ?_
  unfold rawChainOK at h
  unfold rawHeadOK
  simp only [Bool.and_eq_true] at h ⊢
  exact h.1.1

theorem sift_of {wd : List Int} {P : Nat}
    (h : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 wd P = true) :
    siftA 6156 PairJ3.levels PairJ3.baseArr 0 (unpack 6156 13 P) = true := by
  have hS : j3StrongArrs.size = 5 := PJ3Check.binds.2.2.2.1
  obtain ⟨hw, hl⟩ := wordEqK_sound ⟨hS, PJ3Check.binds.2.2.2.2.1⟩ PJ3Check.perm h
  have hrep := rep_wordA (n := 6156) (j := 5) (gs := fun h => permOfArr 6156 j3StrongArrs[h]!)
    (fun h hh => rep_S hd (by omega)) (fun h hh => rep_Si hd (by omega)) wd hl
  rw [hw] at hrep
  refine siftA_fix hd PJ3Check.card_le baseArr.size 0 (by simp) _ _ hrep ?_
  rw [Fix_zero]
  refine (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨i, rfl⟩
  exact S_mem_Gen hd i.val (by omega)

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
open Certificates in
theorem facts12623 :
    eqA 6156 (compA 6156 j3tLines[2]! j3tLines[4]!) (compA 6156 j3tLines[4]! j3tLines[2]!) = true ∧
      eqA 6156 (compA 6156 j3tLines[2]! j3tLines[0]!) (compA 6156 j3tLines[0]! j3tLines[2]!) = true ∧
      eqA 6156 (compA 6156 j3tLines[4]! j3tLines[0]!) (compA 6156 j3tLines[0]! j3tLines[4]!) = true ∧
      (List.range 27).all (fun m => decide (m = 0) ||
        decide (j3fix (j3e27Elt m) = if m % 3 = 0 then 0 else 36)) = true ∧
      (List.range 27).all (fun m => (List.range m).all fun m' =>
        !eqA 6156 (j3e27Elt m) (j3e27Elt m')) = true ∧
      decide (j3fix j3tReps[0]! = 36) = true ∧ decide (j3fix j3tReps[1]! = 0) = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tLines[2]! = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tLines[4]! = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tLines[0]! = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := facts12623a
  refine ⟨a1, a2, a3, a4, a5, a6, a7, ?_, ?_, ?_⟩
  · rw [hL (by norm_num)]
    exact sift_of sw0
  · rw [hL (by norm_num)]
    exact sift_of sw1
  · rw [hL (by norm_num)]
    exact sift_of sw2

end CertificateChecks.KernelSporSch.J3KT

end
