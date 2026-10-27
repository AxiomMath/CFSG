module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.ComponentClassification.J2Cover

@[expose] def abGens : Array (Array Nat) := autStrong.extract 0 2

@[expose] def invReps : List (Array Nat) := [autStrong[0]!, twoAArr]

@[expose] def uReps : List (Array Nat) := [outerArr]

end CertificateChecks.KernelJ2Cover

end
