module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CertificateChecks.KernelLC.ExcO8W

@[expose] def tQWords : List (List ℤ) :=
  [[3, 2], [4, 2], [12, 8], [4, 3], [5, 4], [6, 4], [6, 5], [7, 5], [7, 6]]

@[expose] def s24QWords : List (List ℤ) :=
  [[2, 1], [3, 1], [6, 9, 6], [3, 2], [4, 2], [9, 8, 9], [4, 3], [5, 3]]

@[expose] def s60QWords : List (List ℤ) := [[2, 1], [4, 1], [9, 6], [3, 1], [3, 2], [5, 2]]

@[expose] def s4QWords : List (List ℤ) := [[3, 1], [5, 1], [8, 7], [4, 1], [4, 3], [6, 3, 6, 3]]

@[expose] def s8QWords : List (List ℤ) :=
  [[5, 5, 2], [5, 3, 5, 5, 3, 5, 2], [4, 1], [1, 3, 1], [3, 5, 5, 3, 2]]

end CertificateChecks.KernelLC.ExcO8W

end
