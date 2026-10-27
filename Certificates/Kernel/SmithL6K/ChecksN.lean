module

public import Certificates.Data.Kernel.SmithL6KN
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataN
import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem prc_ok : treeK 1953 1953 (partRootK tcP idxP) (partEdgeK tcP idxP) prt prc = true := by
  decide +kernel

theorem frt_ok : (keyAt fpkL frt == fourKey fourBase && decide (frt < 20160)) = true := by
  decide +kernel

theorem fgm_ok : genOK tcP idxP fgm = true := by decide +kernel

@[expose] noncomputable def ch38609N (k : Nat) : Bool :=
  fourChunkK tcP idxP (keyAt fpkL) (recAt frpL) fgm frt k

#kc_each ch38609N 0 21

end CertificateChecks.KernelSmithL6K
