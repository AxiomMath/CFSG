module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtSD

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def s1G : Array (Array Nat) := decs s1pDecs

meta def c1B : Array Nat := #[0, 2, 1]

end CertificateChecks.KernelSpor.SuzBtSD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtS1 1782 11 CertificateChecks.KernelSpor.SuzBtSD.s1G
  CertificateChecks.KernelSpor.SuzBtSD.c1B

end
