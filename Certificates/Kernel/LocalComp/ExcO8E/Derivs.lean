module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8EInputs
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelLC.ExcO8E

@[expose] def d48L : List (List (ℕ × List ℤ × ℕ)) :=
  [[(1, [7, 5, 1], 1)], [(1, [7, 5, 1], 1)], [(1, [3], 1)], [(1, [1, 3, 1], 1)],
    [(1, [1, 3, 1], 1)], [(1, [7, 5, 1], 1)], [(1, [1, 3, 1], 1)], [(1, [1, 3, 1], 1)], [],
    [(1, [1, 3, 1], 1)], [(1, [1, 3, 1], 1)], [(1, [3], 1)], [(1, [3], 1)], [], [(1, [3], 1)], [],
    [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)],
    [(1, [3], 1)], [(1, [3], 1)], [(1, [1, 3, 1], 1)], [(1, [3], 1)], [(1, [3], 1)],
    [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)],
    [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)], [(1, [1, 3, 1], 1)], [(1, [3], 1)],
    [(1, [3], 1)], [(1, [3], 1)], [(1, [3], 1)], [(1, [1, 3, 1], 1)], [(1, [1, 3, 1], 1)], [], [],
    [(1, [7, 5, 1], 1)], [], [], [(1, [1, 3, 1], 1)]]

@[expose] def d16L : List (List (ℕ × List ℤ × ℕ)) :=
  [[], [], [], [], [], [(1, [5, 1], 1)], [(1, [5, 1], 1)], [(1, [1, 3, 1], 1)], [(1, [5, 1], 1)],
    [(1, [1, 3, 1], 1)], [(1, [7, 1], 1)], [(1, [5, 1], 1)], [], [(1, [5, 1], 1)], [],
    [(1, [5, 1], 1)], [], [], [], [], [], []]

end CertificateChecks.KernelLC.ExcO8E

#ks_chars CertificateChecks.KernelLC.ExcO8E.T48
  CFSG.ComponentClassification.RankTwoClassical.ExcO8E.d48Data

#ks_chars CertificateChecks.KernelLC.ExcO8E.T16
  CFSG.ComponentClassification.RankTwoClassical.ExcO8E.d16Data

end
