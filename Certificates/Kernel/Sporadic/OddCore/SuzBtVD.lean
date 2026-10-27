module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
meta import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtVD

meta def v0G : Array (Array Nat) := CFSG.Sporadic.SuzRecog.C1Model.v0Tabs

meta def c1B : Array Nat := #[0, 2, 1]

end CertificateChecks.KernelSpor.SuzBtVD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtV0 1782 11 CertificateChecks.KernelSpor.SuzBtVD.v0G
  CertificateChecks.KernelSpor.SuzBtVD.c1B

end
