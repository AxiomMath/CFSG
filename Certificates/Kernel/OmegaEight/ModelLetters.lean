module

public import Certificates.Data.Kernel.Spor.Raw
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData

public section

namespace CertificateChecks.KernelO8

open CFSG.KS.Raw CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight.Stage1.Model

theorem kLettersCP : ∀ wd ∈ cands .plus, lettersK 17 wd = true := by decide +kernel

theorem kLettersCM : ∀ wd ∈ cands .minus, lettersK 18 wd = true := by decide +kernel

end CertificateChecks.KernelO8

end
