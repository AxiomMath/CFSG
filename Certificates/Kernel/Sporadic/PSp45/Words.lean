module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData

public section

namespace CertificateChecks.KernelSpor.PSp45

open CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def wordsP : List (List Int) :=
  [[1], [2, 1, 2, 2, 2, 2, 1, 2], [2, 1, 2, 1, 2, 2, 2, 1, 2], [1, 2, 1, 2, 2, 2, 1, 2, 1, 2],
    [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2],
    [2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2]]

@[expose] def wordsA : List (List Int) :=
  [[1], [3], [2, 2, 2, 3, 2, 2], [2, 1, 2, 3, 2, 3, 2], [1, 3], [1, 2, 3, 2, 3, 2, 3, 2],
    [1, 2, 1, 2, 2, 2, 1, 2, 1, 2], [2, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 2, 2]]

@[expose] def invRepWords : List (List Int) :=
  [[1], [2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1]]

@[expose] def invReps : List (Equiv.Perm (Fin 45)) :=
  invRepWords.map (CFSG.Sporadic.Schreier.evalCodes [x45, y45])

@[expose] def ws45N : List (List Nat × Nat) :=
  [([0, 1], 9), ([0, 1, 1], 12), ([0, 1, 0, 1, 1], 6)]

@[expose] def fixWord : List Bool := [true, false, true, true, true, true, false, true]

@[expose] def orbWords : List (List Bool) :=
  [[], [true, true, true, true], [false, true, true, true, true], [false, true, true],
    [true, true, false, true, true], [true, true, false, true, true, false, true], [true, true],
    [false, true, true, false, true, true], [false, true, true, false, true, true, false, true],
    [true, true, true, false, true, false, true, true], [true, false, true, true, false, true, true],
    [false, true, false, true, true, false, true],
    [false, true, true, true, false, true, false, true, true],
    [true, true, true, false, true, true, false, true], [true, false, true, true, false, true],
    [true, true, false, true, true, false, true, true, false, true, true, false, true, true],
    [true, true, true, true, false, true, false, true, true, false, true],
    [true, false, true, false, true, true, false, true], [true, false, true, true],
    [false, true, false, true, false, true, true, false, true],
    [true, false, true, true, false, true, false, true, true], [true, true, false, true],
    [false, true, false, true, true], [false, true, true, false, true], [true, false, true],
    [true, true, false, true, false, true, true, false, true],
    [true, false, true, false, true, true],
    [true, true, false, true, true, false, true, true, false, true, true], [true, true, true],
    [false, true, true, false, true, true, false, true, true, false, true, true],
    [true, true, true, false, true], [false, true, true, false, true, true, false, true, true],
    [false, true, true, true], [true, true, false, true, true, false, true, true],
    [true, true, true, false, true, true, false, true, true, false, true, true, false, true, true],
    [true, true, true, false, true, false, true, true, false, true],
    [true, false, true, true, false, true, true, false, true, true],
    [false, true, true, false, true, false, true, true], [true],
    [true, true, false, true, false, true, true], [true, false, true, true, true],
    [true, false, true, true, false, true, true, false, true, true, false, true, true],
    [false, true],
    [false, true, false, true, true, false, true, true, false, true, true, false, true, true],
    [true, true, true, false, true, true, false, true, true, false, true, true]]

end CertificateChecks.KernelSpor.PSp45

end
