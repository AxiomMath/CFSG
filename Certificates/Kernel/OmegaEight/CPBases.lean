module

public import Init

public section

namespace CertificateChecks.KernelO8

@[expose] def uBaseP : Array Nat := #[0, 2, 4, 16, 32]

@[expose] def uBaseM : Array Nat := #[0, 8, 16]

@[expose] def lBaseM : Array Nat := #[0, 2, 1, 12, 4, 28, 5]

@[expose] def noWords : List (List Int) := []

@[expose] def pBaseP : Array Nat := #[0, 2, 1, 4, 32, 16]

@[expose] def pBaseM : Array Nat := #[0, 8, 1, 16, 36, 2]

@[expose] def pWordsP : List (List Int) := [[-7, 11], [-7, 12], [13, -14, 13], [-7, -8], [-7, -9],
  [-16, -13, -14, -17, -16, -7, -10], [-16, 18, 16], [-19, -15, -13, -7, -17, 11, 8, 18, 7]]

@[expose] def pWordsM : List (List Int) :=
  [[-7, 8], [-7, 9], [-13, 14, 13], [-7, 10], [15, 16, 15], [-7, 11]]

end CertificateChecks.KernelO8

end
