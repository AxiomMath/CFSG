module

public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CertificateChecks.Chain3025

@[expose] def co2Der : List (List Int) :=
  [[-2, -2, -2, 1, 2, 2, 2],
    [1, -2, -2, -2, 1, 2, 2, 2, 1],
    [4, 3, 4],
    [-2, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1],
    [4, -6, 4, 6, 4],
    [3, 4, 3, -6, 4, 6, 3, 4, 3],
    [-6, 3, 4, 3, 4, 6, 6, 4, 3],
    [7, -9, 7, 9, 7],
    [5, 8, -9, 8, 9, 7],
    [11, 11],
    [10, -11, 10, -11, 8, -9, 7, 9, 8],
    [-9, 5, 9, 9, 8],
    [13, 10, -14, 11, 10, 14],
    [15, 12, 15, 12],
    [16, 12, 13, -11, -14, 13, 10, 14, 11, 10],
    [17, 16, 15, 17, 15],
    [12, 13, 15, 10, -11, 14, 11, 14, 10],
    [18, 19, 12, 13, 19, 13]]

meta def strongM : Array (Array Nat) := CFSG.Monster.B.Co2.Native.chainStrong ()

meta def baseM : Array Nat := CFSG.Monster.B.Co2.Native.chainBase

meta def vecsM : Array Nat := CFSG.Monster.B.Co2.Native.vectors ()

end CertificateChecks.Chain3025

end
