module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitData

public section

namespace CertificateChecks.KernelO8.C3850

open CFSG.EvenSmallLie.OmegaEight.NSplit CFSG.EvenSmallLie.OmegaEight.Stage1

theorem gam_plus : nsGamCheck .plus = true := by decide +kernel

theorem gam_minus : nsGamCheck .minus = true := by decide +kernel

theorem h1_plus : nsH1Check .plus = true := by decide +kernel

theorem h1_minus : nsH1Check .minus = true := by decide +kernel

end CertificateChecks.KernelO8.C3850

end
