module

public import Certificates.Kernel.J3T799350.Checks
public import Certificates.Kernel.J3T799350.Base
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Reg
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.Kernel.J3TkSound
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.Certificates.Kernel.Spor.ClassOneH
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
import CFSG.Monster.Code.Weights

public section

namespace CertificateChecks.KernelJ3T799350

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.J3Tk CertificateChecks.KernelSporSch
  CFSG.Sporadic.Schreier
  CFSG.Monster.B.Co2 CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

theorem chunks_le : Nat.ble chunks.length 152 = true := by quickRfl

theorem loopS_eq {j : Nat} (hj : j < j3TData.loops.length) :
    loopS j = loopK RT ET j3TData j3TData.loops[j] := by
  unfold loopS
  generalize j3TData.loops = L at hj ⊢
  induction L generalizing j with
  | nil => simp at hj
  | cons a L ih =>
    cases j with
    | zero => rfl
    | succ j => simpa using ih (j := j) (by simpa using hj)

theorem enums_len : j3TData.enums.length = 11 := by decide

theorem enums_ok : ∀ e < j3TData.enums.length, enumHeadK RT ET j3TData e = true ∧
    ∀ j < cardOf j3TData e / 512 + 1, enumPartK RT ET j3TData e (Nat.mul 512 j) 512 = true := by
  intro e he
  rw [enums_len] at he
  refine ⟨by simpa using allBlk_spec eh e he, fun j hj => ?_⟩
  interval_cases e
  · have : cardOf j3TData 0 = 16 := rfl
    rw [this] at hj; interval_cases j; exact e0
  · have : cardOf j3TData 1 = 1920 := rfl
    rw [this] at hj; interval_cases j
    exacts [e1a, e1b, e1c, e1d]
  · have : cardOf j3TData 2 = 2880 := rfl
    rw [this] at hj; interval_cases j
    exacts [e2a, e2b, e2c, e2d, e2e, e2f]
  · have : cardOf j3TData 3 = 960 := rfl
    rw [this] at hj; interval_cases j
    exacts [e3a, e3b]
  · have : cardOf j3TData 4 = 960 := rfl
    rw [this] at hj; interval_cases j
    exacts [e4a, e4b]
  · have : cardOf j3TData 5 = 64 := rfl
    rw [this] at hj; interval_cases j; exact e5
  · have : cardOf j3TData 6 = 960 := rfl
    rw [this] at hj; interval_cases j
    exacts [e6a, e6b]
  · have : cardOf j3TData 7 = 960 := rfl
    rw [this] at hj; interval_cases j
    exacts [e7a, e7b]
  · have : cardOf j3TData 8 = 27 := rfl
    rw [this] at hj; interval_cases j; exact e8
  · have : cardOf j3TData 9 = 1080 := rfl
    rw [this] at hj; interval_cases j
    exacts [e9a, e9b, e9c]
  · have : cardOf j3TData 10 = 9 := rfl
    rw [this] at hj; interval_cases j; exact e10

theorem loops_ok : ∀ l ∈ j3TData.loops, loopK RT ET j3TData l = true := by
  intro l hl
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  rw [← loopS_eq hj]
  have h11 : j < 11 := by rwa [loops_len] at hj
  interval_cases j
  exacts [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]

theorem slp_ok : ∀ j < 19,
    chunksK RT MT PR PM 57 ((chunks.drop (Nat.mul 8 j)).take 8) (Nat.mul 8 j) = true := by
  intro j hj
  interval_cases j
  exacts [slp0, slp1, slp2, slp3, slp4, slp5, slp6, slp7, slp8, slp9, slp10, slp11, slp12, slp13,
    slp14, slp15, slp16, slp17, slp18]


theorem fixed_le : j3TData.fixedBelow ≤ 19 := le_refl _

theorem strong_rep : ∀ h < 5,
    CFSG.Monster.B.Co2.Rep 6156 (CFSG.KS.Raw.unpack 6156 13 (PJ3.S h)) (j3StrongPerm h) ∧
    CFSG.Monster.B.Co2.Rep 6156 (CFSG.KS.Raw.unpack 6156 13 (PJ3.SI h)) (j3StrongPerm h)⁻¹ := by
  intro h hh
  have e : j3StrongPerm h = permOfArr 6156 (CFSG.KS.Raw.unpack 6156 13 (PJ3.S h)) := by
    rw [← PJ3Check.arr_eq h hh]; rfl
  rw [e]
  exact PJ3Check.rep_g h hh

set_option maxRecDepth 100000 in
theorem tsem : TSem initG (regsOf RT) j3TData := by
  refine tcheckK_sound (RT := RT) (ET := ET) (D := j3TData) (initG := initG) (MT := MT)
    (PS := PJ3.S) (PSI := PJ3.SI) (W := words) (NM := 57)
    (chunks := chunks) (PR := PR) (PM := PM) fixed_le (fun r hr => rep_RT hr)
    (fun r hr => initG_mem hr) strong_rep (fun g hg => base_one hg)
    (Nat.le_of_ble_eq_true chunks_le) slp_ok cover coverMid enums_ok facts loops_ok
    (fun _ hh => CFSG.ComponentClassification.RankTwoSporadic.J3.j3StrongPerm_mem hh) (by decide)

theorem regs : Reg (regsOf RT) := Reg.of_sem tsem

end CertificateChecks.KernelJ3T799350

end
