module

public import Certificates.Data.Kernel.SmithL6KT
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataT

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem ftr_ok : treeK 1953 1953 (· == 0) (convEdgeK tcP idxP) [0] ftr = true := by
  decide +kernel

theorem str_ok : treeK 1953 1953 (fun a => srp.contains a) (stabEdgeK tcP idxP) srp str = true := by
  decide +kernel

theorem reps_ok : repsK tcP = srp := by decide +kernel

theorem reps_cls : (List.range 7).all (fun c => stabClsK tcP (srp.getD c 0) == c) = true := by
  decide +kernel

theorem fix_ok : fixK tcP idxP 0 fxw = true := by decide +kernel

theorem dec_ok : tcl.map (decCols dtb) = tvc := by decide +kernel

theorem card_ok : stabCardK tcP = true := by decide +kernel

theorem comm_ok : stabCommK tcP idxP = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
