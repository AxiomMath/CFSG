module

public import Certificates.Data.Kernel.SmithL6KOp
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataW
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem op_ord4_q : ∀ a < 1953,
    (stabClsK tcP a == 6 || wordId (altW (pairK tcP 0) (pairK tcP a) 4)) = true := by
  kc_cover 245

theorem op_ord4_ok : ord4K tcP = true := by
  unfold ord4K
  exact List.all_eq_true.2 fun a ha => op_ord4_q a (List.mem_range.1 ha)

theorem op_std_ok : stdK tcP = true := by decide +kernel

theorem op_f3_ok : f3K tcP idxP wtP tcl = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
