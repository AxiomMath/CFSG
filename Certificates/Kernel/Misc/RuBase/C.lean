module

public import Certificates.Kernel.Misc.RuBase.Bind
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuBase

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuBase
  CFSG.EvenSporadicStandard.TwoRu.HypOne

theorem permG0 : permOK 4060 12 (mask 12) (4060 * 12) (GC 0) (invP (GC 0)) = true := by quickRfl
theorem permG1 : permOK 4060 12 (mask 12) (4060 * 12) (GC 1) (invP (GC 1)) = true := by quickRfl

theorem wordH0 : Nat.beq (HC 0) (wordP GC (fun l => invP (GC l)) fourHC[0]!) = true := by quickRfl
theorem wordH1 : Nat.beq (HC 1) (wordP GC (fun l => invP (GC l)) fourHC[1]!) = true := by quickRfl
theorem wordH2 : Nat.beq (HC 2) (wordP GC (fun l => invP (GC l)) fourHC[2]!) = true := by quickRfl

theorem permH0 : permOK 4060 12 (mask 12) (4060 * 12) (HC 0) (HIC 0) = true := by quickRfl
theorem permH1 : permOK 4060 12 (mask 12) (4060 * 12) (HC 1) (HIC 1) = true := by quickRfl
theorem permH2 : permOK 4060 12 (mask 12) (4060 * 12) (HC 2) (HIC 2) = true := by quickRfl

theorem powH0 : Nat.beq (powP (HC 0) 5) idP = true := by quickRfl
theorem powH1 : Nat.beq (powP (HC 1) 5) idP = true := by quickRfl
theorem powH2 : Nat.beq (powP (HC 2) 5) idP = true := by quickRfl

theorem pt0 : ptK HC HIC fourPtsC[0]!.1 fourPtsC[0]!.2.1 fourPtsC[0]!.2.2 = true := by quickRfl
theorem pt1 : ptK HC HIC fourPtsC[1]!.1 fourPtsC[1]!.2.1 fourPtsC[1]!.2.2 = true := by quickRfl
theorem pt2 : ptK HC HIC fourPtsC[2]!.1 fourPtsC[2]!.2.1 fourPtsC[2]!.2.2 = true := by quickRfl

theorem fourBaseC_true : fourBaseC = true := by
  have hq : ∀ q ∈ fourPtsC, q.1 < 4060 ∧ q.2.1.all (lettersOK fourHC.length) = true ∧
      q.2.2.all (fun f => lettersOK fourHC.length f.2) = true ∧ ptK HC HIC q.1 q.2.1 q.2.2 = true := by
    intro q hq
    simp only [fourPtsC, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨by decide, by decide, by decide, pt0⟩
    · exact ⟨by decide, by decide, by decide, pt1⟩
    · exact ⟨by decide, by decide, by decide, pt2⟩
  exact fourBaseK_sound (gs := [(CFSG.Sporadic.RuSchreier.ruField4060 1)[0]!,
      (CFSG.Sporadic.RuSchreier.ruField4060 1)[1]!]) rowC
    (fun l hl => by
      have hl2 : l < 2 := hl
      interval_cases l
      exacts [permG0, permG1])
    (by decide)
    (fun i hi => by
      have hi3 : i < 3 := hi
      interval_cases i
      exacts [wordH0, wordH1, wordH2])
    (fun i hi => by
      have hi3 : i < 3 := hi
      interval_cases i
      exacts [permH0, permH1, permH2])
    (fun i hi => by
      have hi3 : i < 3 := hi
      interval_cases i
      exacts [powH0, powH1, powH2])
    hq

end CertificateChecks.KernelMisc.RuBase

end
