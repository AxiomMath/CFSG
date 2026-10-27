module

public import Certificates.Kernel.SporSch.J1.Words
public meta import Certificates.Kernel.SporSch.J1.Words
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_ptmul CertificateChecks.KernelSporSch.J1PD CertificateChecks.KernelSporSch.J1L 3080 12
  CertificateChecks.KernelSporSch.J1.strongM CertificateChecks.KernelSporSch.J1.baseM
  CertificateChecks.KernelSporSch.J1.dGM CertificateChecks.KernelSporSch.J1W.D 200

namespace CertificateChecks.KernelSporSch.J1PD

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MOC CFSG.KS.SporSch.J1C

theorem root : eqB 12 (mask 12) J1L.BP 3 (elJ 3080 12 (mask 12) (3080 * 12) 3 J1L.LR J1L.TR jR)
    (fun x => x) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J1PD

end
