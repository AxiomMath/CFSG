module

public import Certificates.Kernel.YoshQ.DataW
public import Certificates.Kernel.YoshQ.DataM

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ

set_option maxHeartbeats 0 in
theorem e_rec :
    (replayK 16 5 16 4000 E00.GS E00.cnt E00.EP E00.PL E00.POS E00.SM E00.SF = true ∧
      (List.range E00.cnt).map (fldN E00.EP (16 * 5)) = E00.RL) ∧
    (replayK 16 5 16 4000 E01.GS E01.cnt E01.EP E01.PL E01.POS E01.SM E01.SF = true ∧
      (List.range E01.cnt).map (fldN E01.EP (16 * 5)) = E01.RL) ∧
    (replayK 16 5 16 4000 E10.GS E10.cnt E10.EP E10.PL E10.POS E10.SM E10.SF = true ∧
      (List.range E10.cnt).map (fldN E10.EP (16 * 5)) = E10.RL) ∧
    (replayK 16 5 16 4000 E11.GS E11.cnt E11.EP E11.PL E11.POS E11.SM E11.SF = true ∧
      (List.range E11.cnt).map (fldN E11.EP (16 * 5)) = E11.RL) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem s00_rec : replayK 16 5 16 4000 S00.GS S00.cnt S00.EP S00.PL S00.POS S00.SM S00.SF = true ∧
    (List.range S00.cnt).map (fldN S00.EP (16 * 5)) = S00.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem s01_rec : replayK 16 5 16 4000 S01.GS S01.cnt S01.EP S01.PL S01.POS S01.SM S01.SF = true ∧
    (List.range S01.cnt).map (fldN S01.EP (16 * 5)) = S01.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem s10_rec : replayK 16 5 16 4000 S10.GS S10.cnt S10.EP S10.PL S10.POS S10.SM S10.SF = true ∧
    (List.range S10.cnt).map (fldN S10.EP (16 * 5)) = S10.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem s11_rec : replayK 16 5 16 4000 S11.GS S11.cnt S11.EP S11.PL S11.POS S11.SM S11.SF = true ∧
    (List.range S11.cnt).map (fldN S11.EP (16 * 5)) = S11.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem a_rec :
    (replayK 16 5 16 4000 A10.GS A10.cnt A10.EP A10.PL A10.POS A10.SM A10.SF = true ∧
      (List.range A10.cnt).map (fldN A10.EP (16 * 5)) = A10.RL) ∧
    (replayK 16 5 16 4000 A11.GS A11.cnt A11.EP A11.PL A11.POS A11.SM A11.SF = true ∧
      (List.range A11.cnt).map (fldN A11.EP (16 * 5)) = A11.RL) ∧
    (replayK 16 5 16 4000 GE10.GS GE10.cnt GE10.EP GE10.PL GE10.POS GE10.SM GE10.SF = true ∧
      (List.range GE10.cnt).map (fldN GE10.EP (16 * 5)) = GE10.RL) ∧
    (replayK 16 5 16 4000 GE11.GS GE11.cnt GE11.EP GE11.PL GE11.POS GE11.SM GE11.SF = true ∧
      (List.range GE11.cnt).map (fldN GE11.EP (16 * 5)) = GE11.RL) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem gl0_rec : replayK 28 5 16 4000 GL0.GS GL0.cnt GL0.EP GL0.PL GL0.POS GL0.SM GL0.SF = true ∧
    (List.range GL0.cnt).map (fldN GL0.EP (28 * 5)) = GL0.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem gl1_rec : replayK 28 5 16 4000 GL1.GS GL1.cnt GL1.EP GL1.PL GL1.POS GL1.SM GL1.SF = true ∧
    (List.range GL1.cnt).map (fldN GL1.EP (28 * 5)) = GL1.RL := by
  decide +kernel

end CertificateChecks.KernelYoshQ

end
