module

public import Certificates.Kernel.Misc.Perm.HS100.TData
public import Certificates.Kernel.Misc.Perm.HS100.S0Checks
public import Certificates.Data.Kernel.PGrp
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.KC.PGrp
open CFSG.KC.Misc.ArrEnum (memK)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.S0 (Z0)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus (zasTKeys)

theorem sySift : allN 3 (fun k => siftR 100 7 C.LR C.TRI C.BP 5 (TX.F k)) = true := by quickRfl

theorem syMem : memK 512 TT.T Z0 = true := by quickRfl

theorem syComm : allN 512 (fun i =>
    Nat.beq (keyCK 100 7 zasTKeys Z0 (TT.T i)) (keyCK 100 7 zasTKeys (TT.T i) Z0)) = true := by
  quickRfl

end CertificateChecks.KernelMisc.HS100.T

end
