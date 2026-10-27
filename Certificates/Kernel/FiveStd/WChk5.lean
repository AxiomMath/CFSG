module

public import Certificates.Kernel.FiveStd.NChk
public import Certificates.Data.Kernel.FiveStdKW5

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

theorem ww0 : checkWK K1c 409405 81126 82001 (sylInvK SylT 79003 79503) = true := by decide +kernel

theorem ww1 : checkWK K1c 409405 80754 82001 (sylInvK SylT 79003 79503) = true := by decide +kernel

theorem ww2 : checkWK K1c 415680 81126 82001 (sylInvK SylT 79003 79503) = true := by decide +kernel

theorem ww3 : checkWK K1c 415680 18835 29501 (sylInvK SylT 19002 116567) = true := by decide +kernel

end CertificateChecks.FiveStd

end
