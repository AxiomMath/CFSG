module

public import Certificates.Kernel.YoshQ.DataN
public import Certificates.Kernel.YoshQ.DataW
public import Certificates.Kernel.YoshQ.DataM
public import Certificates.Data.Kernel.YoshQ.Twin
public import Certificates.Data.Kernel.YoshQ.Param
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native

set_option maxHeartbeats 0

theorem l8f : l8FactN N10.RL (nTN N10.GS (swN eWord)) = true ∧
    l8FactN N11.RL (nTN N11.GS (swN eWord)) = true ∧
    l8ZNN N10.RL (nTN N10.GS (swN cWord)) (nTN N10.GS (jIn 1 (swN [7, 8]))) E10.RL = true ∧
    l8ZNN N11.RL (nTN N11.GS (swN cWord)) (nTN N11.GS (jIn 1 (swN [7, 8]))) E11.RL = true := by
  decide +kernel

theorem l8c : l8Chain 1 0 (E10.RL.map (tabN 16 5)) = true ∧
    l8Chain 1 1 (E11.RL.map (tabN 16 5)) = true := by
  decide +kernel

theorem syl : ((wgens 1 0 sWords).size == (sylowHomData 0).size && (sylowHomData 0).all (fun T =>
      CFSG.Sporadic.SmallOddCore.permOK 12 T && evenTab T) &&
      !tblEq 16 (nwT 1 0 cWord) (idT 16)) = true ∧
    ((wgens 1 1 sWords).size == (sylowHomData 1).size && (sylowHomData 1).all (fun T =>
      CFSG.Sporadic.SmallOddCore.permOK 12 T && evenTab T) &&
      !tblEq 16 (nwT 1 1 cWord) (idT 16)) = true ∧
    sylowHomOn ((GL0.RL.map (tabN 28 5)).toArray) (nwT 1 0 cWord) = true ∧
    sylowHomOn ((GL1.RL.map (tabN 28 5)).toArray) (nwT 1 1 cWord) = true := by
  decide +kernel

end CertificateChecks.KernelYoshQ

end
