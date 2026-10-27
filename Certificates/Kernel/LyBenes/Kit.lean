module

public import Certificates.Kernel.LyBenes.Data

public section

namespace CertificateChecks.KernelLyB

open CFSG.KC.LyBenes CertificateChecks.KernelLy

theorem bind_ok : kitBindOK NS CS DS = true := by decide +kernel

theorem valid_ok : kitValidOK NS = true := by decide +kernel

theorem inv_ok : kitInvOK NS = true := by decide +kernel

theorem gen_ok : kitGenOK NS = true := by decide +kernel

end CertificateChecks.KernelLyB

end
