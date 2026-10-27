module

public import Certificates.Data.Kernel.Fi22.MarkedK
public import Certificates.Kernel.Fi22LH.Sel

public section

namespace CertificateChecks.KernelFi22Marked

open CFSG.KS.Fi22Marked CFSG.KD.Fi22LH

theorem points_ok : pointsOK pointsData := by
  unfold pointsOK
  decide +kernel

theorem rows_ok : rowsOK R lb0 markedTree pointsData := by
  unfold rowsOK
  decide +kernel

theorem tree_ok : treeOK markedTree pointsData := by
  unfold treeOK
  decide +kernel

end CertificateChecks.KernelFi22Marked
