module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RuThreeData

public section

namespace CertificateChecks.KernelTc.Ru

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

@[expose] def tenGs : Array (Array Nat) := #[ruR0, ruR1]

@[expose] def keys10 : Array Nat := (List.range 10).toArray

end CertificateChecks.KernelTc.Ru

end
