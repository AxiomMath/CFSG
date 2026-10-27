module

public import CFSG.Certificates.Kernel.EvenSporDS81.FCFast
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXData

public section

namespace CertificateChecks.KernelEvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.KC.EvenSporDS81

set_option maxRecDepth 100000 in
theorem ax_treeOK : treeOK (axMs.toList.map keyA) (idxTree (axMs.toList.map keyA)) = true := by
  decide +kernel

theorem ax_tabK_eq : tabK (axMs.toList.map keyA) =
    tabF (axMs.toList.map keyA) (idxTree (axMs.toList.map keyA)) :=
  tabK_eq ax_treeOK

end CertificateChecks.KernelEvenSporDS81
