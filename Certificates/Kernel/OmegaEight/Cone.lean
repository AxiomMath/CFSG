module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitConeData

public section

namespace CertificateChecks.KernelO8

open CFSG.EvenSmallLie.OmegaEight

theorem cone_plus : Chain.splitConeCheck .plus = true := by decide +kernel

theorem cone_minus : Chain.splitConeCheck .minus = true := by decide +kernel

theorem cert3496 : Chain.splitConeCheck .plus = true ∧ Chain.splitConeCheck .minus = true :=
  ⟨cone_plus, cone_minus⟩

end CertificateChecks.KernelO8

end
