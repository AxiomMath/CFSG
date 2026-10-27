module

public import Certificates.Data.Kernel.EvenSporDS81.FCDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXData

public section

namespace CertificateChecks.KernelEvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.KC.EvenSporDS81

set_option maxRecDepth 100000

theorem ax_cols : axMs.toList.all fcColsLt = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ax_dist : fcDistinct axMs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ax_words : axWordsOKL axGc axQs axWs axMs = true := by
  decide +kernel

end CertificateChecks.KernelEvenSporDS81
