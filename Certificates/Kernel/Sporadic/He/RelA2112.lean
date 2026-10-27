module

public import Certificates.Kernel.Sporadic.He.Gens2112
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2112

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen TauCeti

theorem rel0 : Nat.beq (wordPK 8330 14 G GI (CFSG.KD.OrdHe.rels.getD 0 [])) (pidn 8330 14) =
    true := by quickRfl
theorem rel1 : Nat.beq (wordPK 8330 14 G GI (CFSG.KD.OrdHe.rels.getD 1 [])) (pidn 8330 14) =
    true := by quickRfl
theorem rel3 : Nat.beq (wordPK 8330 14 G GI (CFSG.KD.OrdHe.rels.getD 3 [])) (pidn 8330 14) =
    true := by quickRfl
theorem rel5 : Nat.beq (wordPK 8330 14 G GI (CFSG.KD.OrdHe.rels.getD 5 [])) (pidn 8330 14) =
    true := by quickRfl
end CertificateChecks.KernelSpor.He2112

end
