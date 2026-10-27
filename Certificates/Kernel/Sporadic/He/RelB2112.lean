module

public import Certificates.Kernel.Sporadic.He.Gens2112
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2112

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen TauCeti

theorem rel2 : Nat.beq (wordPK 8330 14 G GI (CFSG.KD.OrdHe.rels.getD 2 [])) (pidn 8330 14) =
    true := by quickRfl
end CertificateChecks.KernelSpor.He2112

end
