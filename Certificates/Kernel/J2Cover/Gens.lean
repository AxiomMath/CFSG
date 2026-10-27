module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelData

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Kernel

@[expose] def crAGens : Array (Array Nat) := crAStrong.extract 0 3

@[expose] def cpTGens : Array (Array Nat) := cent2AStrong.extract 0 2

@[expose] def crTGens : Array (Array Nat) := crTStrong.extract 0 3

@[expose] def crUGens : Array (Array Nat) := crUStrong.extract 0 3

end CertificateChecks.KernelJ2Cover

end
