module

public import Certificates.Kernel.Fi22Core.Assemble
public import Certificates.Kernel.Fi22Core.Card

public section

namespace CertificateChecks.KernelFi22C

open CFSG.Sporadic.Fi22.Native CFSG.F3.Native

theorem fi22_cert :
    (matrixChecks () && conjOrbitOK 77 (matA ()) (matA ()) (matB ()) (matBi ()) orbL 3 &&
      actionChecks orbL 3 && productChecks orbL) = true :=
  fi22_cert_of letters_card

end CertificateChecks.KernelFi22C

end
