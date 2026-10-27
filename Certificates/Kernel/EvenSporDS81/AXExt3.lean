module

public import Certificates.Kernel.EvenSporDS81.AXIdx

public section

namespace CertificateChecks.KernelEvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.KC.EvenSporDS81

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_ext3 : extOKG (tabK (axMs.toList.map keyA)) (idxL axMs.toList idColsK) axMs.size
    ((axFam.drop (90 * 3)).take 90) axFam = true := by
  rw [extOKG_tabK ax_treeOK 8]
  decide +kernel

end CertificateChecks.KernelEvenSporDS81
