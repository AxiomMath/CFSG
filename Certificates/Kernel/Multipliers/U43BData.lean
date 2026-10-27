module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CertificateChecks.KernelU43B

@[expose] def base : Array Nat := #[0, 1, 9]

@[expose] def der : List (List Int) :=
  [[-1, 2, -1, -2, -2, 1, -2, 1], [-1, -2, 3, 2, 1], [-1, -4, -2, -4, -2, 1], [-3, -4, 5, 4, 3],
    [-4, -3, 5, 3, 4]]

end CertificateChecks.KernelU43B

end
