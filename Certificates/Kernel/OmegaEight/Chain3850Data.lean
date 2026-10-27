module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitData

public section

namespace CertificateChecks.KernelO8.Chain3850

open CFSG.EvenSmallLie.OmegaEight.NSplit CFSG.EvenSmallLie.OmegaEight.Stage1

@[expose] def strongP : Array (Array Nat) := strong .plus

@[expose] def strongM : Array (Array Nat) := strong .minus

@[expose] def baseP : Array Nat := chainBasePlus.toArray

@[expose] def baseM : Array Nat := chainBaseMinus.toArray

end CertificateChecks.KernelO8.Chain3850

end
