module

public import Certificates.Kernel.WordRelK.Tab
public import Certificates.Data.Kernel.WordRelK
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.WordRelK CertificateChecks.KernelWordRelK.Tab in
#kc_each CertificateChecks.KernelWordRelK.Small usq (uSqT TAB) 0 10

open CFSG.KC.WordRelK CertificateChecks.KernelWordRelK.Tab in
#kc_each CertificateChecks.KernelWordRelK.Small co (coDecT TAB) 0 9

open CFSG.KC.WordRelK CertificateChecks.KernelWordRelK.Tab in
#kc_each CertificateChecks.KernelWordRelK.Small pa (paDecT TAB) 0 15

namespace CertificateChecks.KernelWordRelK.Small

open CFSG.KC.WordRelK

theorem lCommSym : lCommSymOK = true := by decide +kernel

theorem uCommDiag : uCommDiagOK = true := by decide +kernel

theorem lengths : lengthsOK = true := by decide +kernel

end CertificateChecks.KernelWordRelK.Small

end
