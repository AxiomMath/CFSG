
module

public import Certificates.Kernel.Sporadic.SuzK.Action

public section

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.Sporadic.Suz.Native

theorem suz_cert : suzCertificate 3 = true := by
  unfold suzCertificate
  rw [matrix_ok, form_ok]
  dsimp only
  rw [orbitData_eq, conj_okW, action_ok]
  rfl

end CertificateChecks.KernelSpor.SuzK

end
