module

public import Init

public section

namespace CertificateChecks.KernelSmallSpor.Sp6S

@[expose] def base1 : Array Nat := #[0, 1, 4, 2, 12]

@[expose] def base2 : Array Nat := #[0, 1, 4, 2]

@[expose] def base3 : Array Nat := #[0, 1, 2, 4]

@[expose] def sWords1 : List (List Int) :=
  [[2, 5, 4, 4, 4, 4, 5, 2, 3, 1], [3, 4, 2, 3, 4, 3, 4, 1], [5, 4, 4, 4, 4, 5, 4, 4, 4, 4],
    [4, 4, 5, 4, 5, 3, 2, 1]]

@[expose] def sWords2 : List (List Int) :=
  [[2, 3, 1, 1, 2], [1, 1, 2, 1, 3, 1, 1], [2, 1, 3, 2, 1, 1, 3, 2, 1],
    [1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 1]]

@[expose] def sWords3 : List (List Int) :=
  [[4, 6, 4, 2, 1], [6, 3, 4, 5, 6, 1], [4, 3, 3, 4, 3, 3, 2], [3, 6, 4, 5, 4, 3, 2]]

@[expose] def sWords4 : List (List Int) :=
  [[5, 6, 3, 2], [6, 4, 5, 2], [4, 5, 6, 3, 1], [5, 4, 6, 6, 4, 1], [6, 5, 6, 5, 4]]

end CertificateChecks.KernelSmallSpor.Sp6S

end
