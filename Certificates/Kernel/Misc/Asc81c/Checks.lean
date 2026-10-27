module

public import Certificates.Kernel.Misc.Asc81c.Data
import all Init.Data.Nat.Fold
import all Init.Data.List.Basic
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check

#kc_each chunk4 0 16

#kc_each chunk3 0 8

theorem neg : (!pairW 4 (x0 4) [14, 11, 2, 1] (1 + 4 * (299 % 128 + 128)) &&
    !pairW 4 (x0 4) [9, 3, 5, 1] (1 + 4 * 18)) = true := by
  decide +kernel

end CertificateChecks.KernelAsc81c

end
