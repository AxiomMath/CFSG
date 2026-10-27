module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcSp6Inputs
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelLC.ExcSp6

@[expose] def daL : List (List (ℕ × List ℤ × ℕ)) :=
  [[(1, [-6, -2, -4, 6, 5, 6, 5, 6], 1)],
    [(1, [-5, -4, -7, -4, 3, 4, 3, 7], 1)],
    [], [], [], [],
    [(1, [-2, -6, -4, -4, 5, 5, 6, 2, 5, 3], 1), (1, [-2, -3, -5, -6, -3, 4, 7, 7, 5, 7], 1)],
    [],
    [(1, [-2, -5, -3, -7, -4, 2, 4, 7, 5, 6], 1)],
    [], [], [], [], [],
    [(1, [-5, -6, -3, -7, 2, 7, 3, 6, 5], 1)],
    [], [], []]

@[expose] def dbL : List (List (ℕ × List ℤ × ℕ)) :=
  [[(1, [-5, -3, -7, -7, -5, -5, 6, 4, 7, 5, 5, 3, 7], 1)],
    [],
    [(1, [-2, -6, -4, -3, -6, -7, 6, 4, 7, 4, 7, 6, 2], 1)],
    [],
    [(1, [-3, -7, -6, -6, 5, 7, 5, 3, 2], 1)],
    [(1, [-2, -6, -6, -3, 4, 5, 6, 6, 5, 2], 1)],
    [(1, [-3, -4, -7, -4, -4, 2, 5, 3, 4, 6, 3], 1),
      (1, [-4, -6, -3, -7, -7, 5, 3, 7, 4, 5, 5, 2], 2)],
    [(1, [-2, -7, -5, -4, -7, -6, 4, 2, 7, 6, 6, 7, 5, 3], 1)],
    [(1, [-3, -5, -7, -7, -7, -2, -6, 5, 3, 4, 7, 7, 7, 5, 3], 1),
      (1, [-4, -3, -7, -6, -6, -4, 7, 4, 4, 2, 7, 4, 2], 1)],
    [(1, [-2, -5, -3, -6, -7, -7, 4, 2, 7, 7, 7, 7, 3], 1),
      (1, [-2, -6, -6, -7, -4, -5, 6, 4, 4, 3, 7, 6, 6], 2)],
    [],
    [(1, [-2, -5, -7, -6, -4, -3, -5, 7, 5, 5, 2, 7, 7, 6], 1),
      (1, [-6, -2, -5, -7, -7, -6, 7, 5, 7, 4, 5, 6, 4], 1)],
    [(1, [-4, -6, -7, -2, -6, 7, 5, 6, 7, 6, 3, 6], 1)],
    [(1, [-5, -3, -6, -3, -6, -3, 2, 5, 5, 6, 6, 7, 2], 1)],
    [(1, [-3, -6, -2, -4, -7, -6, 5, 4, 3, 7, 5, 7], 1),
      (1, [-2, -6, -4, -3, -7, -7, 2, 7, 6, 3, 7, 5, 3], 1)]]

end CertificateChecks.KernelLC.ExcSp6

#ks_chars CertificateChecks.KernelLC.ExcSp6.DaT
  CFSG.ComponentClassification.RankTwoClassical.ExcSp6.daData

#ks_chars CertificateChecks.KernelLC.ExcSp6.DbT
  CFSG.ComponentClassification.RankTwoClassical.ExcSp6.dbData

end
