module

public import Certificates.Data.Kernel.EvenSporDS81.ExtDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXData

public section

namespace CertificateChecks.KernelEvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.KC.EvenSporDS81

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_head : axHeadL axMs.toList axFam = true := by
  decide +kernel

end CertificateChecks.KernelEvenSporDS81
