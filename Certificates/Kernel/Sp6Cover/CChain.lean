module

public import Certificates.Kernel.Sp6Cover.Data
public import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Kernel.Sp6Cover.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSp6Cover.CC 240 8 0 CertificateChecks.KernelSp6Cover.cS
  CertificateChecks.KernelSp6Cover.cBase 3 CertificateChecks.KernelSp6Cover.cWD

namespace CertificateChecks.KernelSp6Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem cbind : cS.size = 6 ∧ (∀ j < 6, cS[j]! = unpack 240 8 (CC.S j)) ∧ cBase.size = 3 ∧
    ∀ t < 3, cBase[t]! = pg 8 (mask 8) CC.BP t := by
  decide +kernel

theorem cperm : allN 6 (fun j => permOK 240 8 (mask 8) (240 * 8) (CC.S j) (CC.SI j)) = true := by
  quickRfl

theorem csizes : (List.range 3).map (fun i => rcnt (CC.LR i)) = [192, 12, 2] := by
  decide +kernel

end CertificateChecks.KernelSp6Cover

end
