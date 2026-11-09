module

public import Certificates.Kernel.SmithL6Coll.Chk
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelSmithL6Coll

open CFSG.SmithL6.CollK

#kc_each rows 16 20

theorem rows20_q : ∀ i < 21, rowK LM (21 * nat_lit 20 + i) = true := by
  kc_cover 3

theorem rows20 : rows (nat_lit 20) = true := by
  unfold rows rowsK
  exact List.all_eq_true.2 fun i hi => rows20_q i (List.mem_range.1 hi)

#kc_each rows 21 24

end CertificateChecks.KernelSmithL6Coll
