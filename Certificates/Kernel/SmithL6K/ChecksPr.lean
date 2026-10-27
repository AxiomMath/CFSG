module

public import Certificates.Data.Kernel.SmithL6KPr
public import Certificates.Data.Kernel.SmithL6KP
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataW
public import Certificates.Kernel.SmithL6K.DataPr
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem ptr_ok : treeK 1395 6 (· == 0) (pEdgeK gpP) [0] ptr = true := by decide +kernel

theorem wmk_nodup : CFSG.Decide.bitsetNodup (wmk.map (· % mkm)) = true := by decide +kernel

theorem row0_ok : row0K wtP wmP = true := by decide +kernel

theorem dist2_row0 : dist2K wmk (wmk.take 1) = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
