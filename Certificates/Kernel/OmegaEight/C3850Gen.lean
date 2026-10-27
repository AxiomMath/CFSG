module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitData

public section

namespace CertificateChecks.KernelO8.C3850

open CFSG.EvenSmallLie.OmegaEight.NSplit CFSG.EvenSmallLie.OmegaEight.Stage1

theorem gen_plus : nsGenCheck .plus = true := by decide +kernel

theorem gen_minus : nsGenCheck .minus = true := by decide +kernel

theorem rel_plus : nsRelCheck .plus = true := by decide +kernel

theorem rel_minus : nsRelCheck .minus = true := by decide +kernel

end CertificateChecks.KernelO8.C3850

end
