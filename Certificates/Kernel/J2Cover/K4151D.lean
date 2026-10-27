module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData

public section

namespace CertificateChecks.KernelJ2Cover

@[expose] def subStrong : Array (Array Nat) :=
  CFSG.ComponentClassification.J2Cover.autStrong.extract 2 7

@[expose] def subBase : Array Nat := #[4, 3]

end CertificateChecks.KernelJ2Cover

end
