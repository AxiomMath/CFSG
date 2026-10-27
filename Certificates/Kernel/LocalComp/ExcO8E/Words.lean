module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CertificateChecks.KernelLC.ExcO8E

@[expose] def seWords : List (List ℤ) := [[1], [3], [5], [7]]

@[expose] def seQWords : List (List ℤ) := [[2, 1, 2], [2, 3, 2], [4, 1, 4, 2], [3, 1], [3, 1, 3, 1]]

@[expose] def s48QWords : List (List ℤ) := [[2, 1], [5, 1], [6, 2, 6], [3, 6, 3, 1], [4, 3]]

@[expose] def s16QWords : List (List ℤ) := [[3, 2, 2], [1, 1]]

end CertificateChecks.KernelLC.ExcO8E

end
