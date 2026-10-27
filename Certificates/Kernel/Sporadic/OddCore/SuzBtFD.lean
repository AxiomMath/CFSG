module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtFD

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def m21G : Array (Array Nat) := decs m21Decs

meta def kG : Array (Array Nat) := decs l1CompDecs

meta def c1B : Array Nat := #[0, 2, 1]

end CertificateChecks.KernelSpor.SuzBtFD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtM21 1782 11 CertificateChecks.KernelSpor.SuzBtFD.m21G
  CertificateChecks.KernelSpor.SuzBtFD.c1B

#kbtup CertificateChecks.KernelSpor.SuzBtK 1782 11 CertificateChecks.KernelSpor.SuzBtFD.kG
  CertificateChecks.KernelSpor.SuzBtFD.c1B

end
