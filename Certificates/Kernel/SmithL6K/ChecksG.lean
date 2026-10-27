module

public import Certificates.Data.Kernel.SmithL6KG
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataG

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem gns_ok : ((gns.all fun g => decide (g < 1953)) && gns.getD 0 1 == 0) = true := by
  decide +kernel

theorem gtr_ok : treeK 1953 gns.length (· == 0) (gEdgeK tcP idxP gns) [0] gtr = true := by
  decide +kernel

theorem formG_ok : formGK gns tcl = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
