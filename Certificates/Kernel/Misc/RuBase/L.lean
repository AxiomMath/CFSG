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

theorem permGL0 : permOK 4060 12 (mask 12) (4060 * 12) (GL 0) (invP (GL 0)) = true := by quickRfl
theorem permGL1 : permOK 4060 12 (mask 12) (4060 * 12) (GL 1) (invP (GL 1)) = true := by quickRfl
theorem permGL2 : permOK 4060 12 (mask 12) (4060 * 12) (GL 2) (invP (GL 2)) = true := by quickRfl

theorem wordHL0 : Nat.beq (HL 0) (wordP GL (fun l => invP (GL l)) fourHL[0]!) = true := by quickRfl
theorem wordHL1 : Nat.beq (HL 1) (wordP GL (fun l => invP (GL l)) fourHL[1]!) = true := by quickRfl

theorem permHL0 : permOK 4060 12 (mask 12) (4060 * 12) (HL 0) (HIL 0) = true := by quickRfl
theorem permHL1 : permOK 4060 12 (mask 12) (4060 * 12) (HL 1) (HIL 1) = true := by quickRfl

theorem powHL0 : Nat.beq (powP (HL 0) 13) idP = true := by quickRfl
theorem powHL1 : Nat.beq (powP (HL 1) 13) idP = true := by quickRfl

theorem ptL0 : ptK HL HIL fourPtsL[0]!.1 fourPtsL[0]!.2.1 fourPtsL[0]!.2.2 = true := by quickRfl
theorem ptL1 : ptK HL HIL fourPtsL[1]!.1 fourPtsL[1]!.2.1 fourPtsL[1]!.2.2 = true := by quickRfl

theorem fourBaseL_true : fourBaseL = true := by
  have hq : ∀ q ∈ fourPtsL, q.1 < 4060 ∧ q.2.1.all (lettersOK fourHL.length) = true ∧
      q.2.2.all (fun f => lettersOK fourHL.length f.2) = true ∧ ptK HL HIL q.1 q.2.1 q.2.2 = true := by
    intro q hq
    simp only [fourPtsL, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨by decide, by decide, by decide, ptL0⟩
    · exact ⟨by decide, by decide, by decide, ptL1⟩
  exact fourBaseK_sound (gs := [(CFSG.Sporadic.RuSchreier.ruField4060 5)[0]!,
      (CFSG.Sporadic.RuSchreier.ruField4060 5)[1]!, (CFSG.Sporadic.RuSchreier.ruField4060 5)[2]!])
    rowL
    (fun l hl => by
      have hl3 : l < 3 := hl
      interval_cases l
      exacts [permGL0, permGL1, permGL2])
    (by decide)
    (fun i hi => by
      have hi2 : i < 2 := hi
      interval_cases i
      exacts [wordHL0, wordHL1])
    (fun i hi => by
      have hi2 : i < 2 := hi
      interval_cases i
      exacts [permHL0, permHL1])
    (fun i hi => by
      have hi2 : i < 2 := hi
      interval_cases i
      exacts [powHL0, powHL1])
    hq

end CertificateChecks.KernelMisc.RuBase

end
