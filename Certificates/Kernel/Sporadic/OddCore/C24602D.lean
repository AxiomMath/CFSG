module

import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#kc_repo #kc_json_gz_eval CertificateChecks.KernelSpor.C24602D
  "Certificates/Kernel/Sporadic/OddCore/data/c24602k.json.gz" 318746 11121961898421497174
  (N : Nat) (root : Nat) (pl : Array Nat)

public section

namespace CertificateChecks.KernelSpor.C24602D

@[expose] def w8 : List (List Int) :=
  [[-3, -3, 2, -3, -3, -3, -2], [-5, -1, 2, 5, -3, -3, -3, 4, -3, -2, 3, 1, 3, -2]]

@[expose] def w27 : List (List Int) :=
  [[-4, -2, -3, 4], [-2, 3, -2, -4, 5, -3, -4, 5, -3, 2, -3, 2],
    [-5, 3, 3, -2, -3, 5, -4, 3, 4, -3, -3, -2, 3]]

@[expose] def w5 : List (List Int) := [[-2, -5, -1, 5, -3, 2, 3, 1, 5, 3, 3]]

end CertificateChecks.KernelSpor.C24602D

end
