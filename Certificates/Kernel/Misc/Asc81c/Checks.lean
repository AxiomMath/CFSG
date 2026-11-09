module

public import Certificates.Kernel.Misc.Asc81c.Lin
import all Init.Data.Nat.Fold
import all Init.Data.List.Basic
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check

#kc_each chunkL4 0 16

#kc_each chunkL3 0 8

theorem neg : (!pairWL 4 (x0c 4) [14, 11, 2, 1] (1 + 4 * (299 % 128 + 128)) &&
    !pairWL 4 (x0c 4) [9, 3, 5, 1] (1 + 4 * 18)) = true := by
  decide +kernel

end CertificateChecks.KernelAsc81c

end
