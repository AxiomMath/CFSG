module

public import Certificates.Kernel.EvenSporDS81.AXIdx

public section

namespace CertificateChecks.KernelEvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.KC.EvenSporDS81

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_tab1 : tabAllL (((tabK (axMs.toList.map keyA)).drop (64 * 1)).take 64) axMs.size = true := by
  rw [ax_tabK_eq]
  decide +kernel

end CertificateChecks.KernelEvenSporDS81
