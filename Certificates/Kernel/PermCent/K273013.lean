module

public import CFSG.GH74.KGroups.L33Inputs
public import Certificates.Data.Kernel.PermCent.CV

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkCV

theorem k273013 :
    (elemsC QA).all (fun g => !(orderIsP g 26 [2, 13]) && !(orderIsP g 39 [3, 13])) = true := by
  decide +kernel

end CertificateChecks.KernelPermCent
