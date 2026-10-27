module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtD

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def m1G : Array (Array Nat) := decs m1Decs

meta def c1B : Array Nat := #[0, 2, 1]

end CertificateChecks.KernelSpor.SuzBtD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtM1 1782 11 CertificateChecks.KernelSpor.SuzBtD.m1G
  CertificateChecks.KernelSpor.SuzBtD.c1B

end
