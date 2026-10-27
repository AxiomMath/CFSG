module

public import Certificates.Kernel.YoshQ.DataM

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ

set_option maxHeartbeats 0 in
theorem y_rec : replayK 14 5 14 2000 Y.GS Y.cnt Y.EP Y.PL Y.POS Y.SM Y.SF = true ∧
    (List.range Y.cnt).map (fldN Y.EP (14 * 5)) = Y.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem k_rec : replayK 14 5 14 4000 K.GS K.cnt K.EP K.PL K.POS K.SM K.SF = true ∧
    (List.range K.cnt).map (fldN K.EP (14 * 5)) = K.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem r_rec : replayK 14 5 14 4000 R.GS R.cnt R.EP R.PL R.POS R.SM R.SF = true ∧
    (List.range R.cnt).map (fldN R.EP (14 * 5)) = R.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem eg_rec : replayK 16 5 16 4000 EG.GS EG.cnt EG.EP EG.PL EG.POS EG.SM EG.SF = true ∧
    (List.range EG.cnt).map (fldN EG.EP (16 * 5)) = EG.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem q00_rec : replayK 24 5 24 4000 Q00.GS Q00.cnt Q00.EP Q00.PL Q00.POS Q00.SM Q00.SF = true ∧
    (List.range Q00.cnt).map (fldN Q00.EP (24 * 5)) = Q00.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem q01_rec : replayK 24 5 24 4000 Q01.GS Q01.cnt Q01.EP Q01.PL Q01.POS Q01.SM Q01.SF = true ∧
    (List.range Q01.cnt).map (fldN Q01.EP (24 * 5)) = Q01.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem q10_rec : replayK 24 5 24 4000 Q10.GS Q10.cnt Q10.EP Q10.PL Q10.POS Q10.SM Q10.SF = true ∧
    (List.range Q10.cnt).map (fldN Q10.EP (24 * 5)) = Q10.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem q11_rec : replayK 24 5 24 4000 Q11.GS Q11.cnt Q11.EP Q11.PL Q11.POS Q11.SM Q11.SF = true ∧
    (List.range Q11.cnt).map (fldN Q11.EP (24 * 5)) = Q11.RL := by
  decide +kernel

end CertificateChecks.KernelYoshQ

end
