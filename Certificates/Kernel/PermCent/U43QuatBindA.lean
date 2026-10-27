module

public import Certificates.Kernel.PermCent.U43QuatP

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43.Quat

theorem bindsQA : (List.range' 0 7).all (fun j =>
    matOK (quatEls.getD j (0, false)).1 (quatEls.getD j (0, false)).2 (QP j)) = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
