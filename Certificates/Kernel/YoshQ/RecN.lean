module

public import Certificates.Kernel.YoshQ.DataN
public import Certificates.Kernel.YoshQ.DataM
public import Certificates.Data.Kernel.YoshQ.Idx

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ

set_option maxHeartbeats 0 in
theorem n00_rec : replayK 16 5 16 4000 N00.GS N00.cnt N00.EP N00.PL N00.POS N00.SM N00.SF = true ∧
    (List.range N00.cnt).map (fldN N00.EP (16 * 5)) = N00.RL ∧
    idxOK 16 5 N00.cnt N00.EP N00.IX = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem n01_rec : replayK 16 5 16 4000 N01.GS N01.cnt N01.EP N01.PL N01.POS N01.SM N01.SF = true ∧
    (List.range N01.cnt).map (fldN N01.EP (16 * 5)) = N01.RL ∧
    idxOK 16 5 N01.cnt N01.EP N01.IX = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem n10_rec : replayK 16 5 16 4000 N10.GS N10.cnt N10.EP N10.PL N10.POS N10.SM N10.SF = true ∧
    (List.range N10.cnt).map (fldN N10.EP (16 * 5)) = N10.RL ∧
    idxOK 16 5 N10.cnt N10.EP N10.IX = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem n11_rec : replayK 16 5 16 4000 N11.GS N11.cnt N11.EP N11.PL N11.POS N11.SM N11.SF = true ∧
    (List.range N11.cnt).map (fldN N11.EP (16 * 5)) = N11.RL ∧
    idxOK 16 5 N11.cnt N11.EP N11.IX = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ne_rec :
    (replayK 16 5 16 4000 NE00.GS NE00.cnt NE00.EP NE00.PL NE00.POS NE00.SM NE00.SF = true ∧
      (List.range NE00.cnt).map (fldN NE00.EP (16 * 5)) = NE00.RL) ∧
    (replayK 16 5 16 4000 NE01.GS NE01.cnt NE01.EP NE01.PL NE01.POS NE01.SM NE01.SF = true ∧
      (List.range NE01.cnt).map (fldN NE01.EP (16 * 5)) = NE01.RL) ∧
    (replayK 16 5 16 4000 NE10.GS NE10.cnt NE10.EP NE10.PL NE10.POS NE10.SM NE10.SF = true ∧
      (List.range NE10.cnt).map (fldN NE10.EP (16 * 5)) = NE10.RL) ∧
    (replayK 16 5 16 4000 NE11.GS NE11.cnt NE11.EP NE11.PL NE11.POS NE11.SM NE11.SF = true ∧
      (List.range NE11.cnt).map (fldN NE11.EP (16 * 5)) = NE11.RL) := by
  decide +kernel

end CertificateChecks.KernelYoshQ

end
