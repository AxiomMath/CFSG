module

public import Certificates.Kernel.YoshQ.DataN
public import Certificates.Kernel.YoshQ.DataM
public import Certificates.Data.Kernel.YoshQ.Twin
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh

set_option maxHeartbeats 0

theorem nc_e : normCenRestN 16 5 EG.GS EG.GS EG.RL EG.RL
    (modelTN 16 5 6 EG.GS [(0, true), (0, true)]) = true ∧
    CFSG.Sporadic.SmallOddCore.permOK 16 eCT = true := by
  decide +kernel

theorem nc_00 : normCenRestN 16 5 N00.GS NE00.GS N00.RL NE00.RL
    (modelTN 16 5 9 N00.GS [(0, true), (0, true)]) = true ∧
    CFSG.Sporadic.SmallOddCore.permOK 16 (nCT 0 0) = true := by
  decide +kernel

theorem nc_01 : normCenRestN 16 5 N01.GS NE01.GS N01.RL NE01.RL
    (modelTN 16 5 9 N01.GS [(0, true), (0, true)]) = true ∧
    CFSG.Sporadic.SmallOddCore.permOK 16 (nCT 0 1) = true := by
  decide +kernel

theorem nc_10 : normCenRestN 16 5 N10.GS NE10.GS N10.RL NE10.RL
    (modelTN 16 5 9 N10.GS [(0, true), (0, true)]) = true ∧
    CFSG.Sporadic.SmallOddCore.permOK 16 (nCT 1 0) = true := by
  decide +kernel

theorem nc_11 : normCenRestN 16 5 N11.GS NE11.GS N11.RL NE11.RL
    (modelTN 16 5 9 N11.GS [(0, true), (0, true)]) = true ∧
    CFSG.Sporadic.SmallOddCore.permOK 16 (nCT 1 1) = true := by
  decide +kernel

end CertificateChecks.KernelYoshQ

end
