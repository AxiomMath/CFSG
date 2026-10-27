module

public import Certificates.Data.TabSuzC

public section

namespace CertificateChecks.KernelSuzC17323

open CFSG.HardMathSupport.Dickson.I271.TabSuzC CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

@[expose] def aGs : Array (Array Nat) := aGens (levels ())

@[expose] def sGs : Array (Array Nat) := sGens (levels ())

@[expose] def keys : Array Nat := cKeys.toArray

end CertificateChecks.KernelSuzC17323

end
