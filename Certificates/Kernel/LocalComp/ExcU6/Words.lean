module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase

public section

namespace CertificateChecks.KernelLC.ExcU6

open CFSG.EvenSmallLie.UnitarySix

@[expose] def s2QWords : List (List ℤ) :=
  [[1], [4], [-8, -1, -3, -2, -3, -5, 1, 5, 3, 2, 3], [-1, -8, -3, -6, -8, -11, 6, 5, 3, 2, 3]]

@[expose] def s3QWords : List (List ℤ) := [[1], [2], [-4, -7, 5, 6]]

@[expose] def o1Word : List ℤ :=
  [12, 17, 46, 8, -46, -17, 16, 46, 2, -46, -16, 7, 46, 2, -46, -7, 16, 46, -2, -46, -16, -12]

@[expose] def o2Word : List ℤ := [12, 16, 46, 2, -46, -16]

@[expose] def letterWords : List (List ℤ) := (List.range 46).map fun k : ℕ => [Int.ofNat k + 1]

@[expose] def alWords : List (List ℤ) :=
  letterWords ++ aWords ++ kWords ++ tWords ++ [o1Word, o2Word]

@[expose] def encZ (z : ℤ) : ℕ := if 0 < z then 2 * (z.toNat - 1) else 2 * ((-z).toNat - 1) + 1

@[expose] def alWN : List (List ℕ) := alWords.map (List.map encZ)

end CertificateChecks.KernelLC.ExcU6

end
