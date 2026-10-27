module

public import Certificates.Data.Kernel.TransvK

public section

namespace CertificateChecks.KernelTransvK

open CFSG.EvenSporadicStandard.ThStd.LocalDataTh CFSG.KC.TransvK

theorem tA0 : TFactsA 0 = true := by decide +kernel
theorem tA1 : TFactsA 1 = true := by decide +kernel
theorem tA2 : TFactsA 2 = true := by decide +kernel
theorem tA3 : TFactsA 3 = true := by decide +kernel
theorem tA4 : TFactsA 4 = true := by decide +kernel
theorem tA5 : TFactsA 5 = true := by decide +kernel
theorem tA6 : TFactsA 6 = true := by decide +kernel
theorem tA7 : TFactsA 7 = true := by decide +kernel
theorem tA8 : TFactsA 8 = true := by decide +kernel
theorem tA9 : TFactsA 9 = true := by decide +kernel
theorem tA10 : TFactsA 10 = true := by decide +kernel
theorem tA11 : TFactsA 11 = true := by decide +kernel
theorem tA12 : TFactsA 12 = true := by decide +kernel
theorem tA13 : TFactsA 13 = true := by decide +kernel
theorem tA14 : TFactsA 14 = true := by decide +kernel
theorem tA15 : TFactsA 15 = true := by decide +kernel

theorem TFactsA_ok : ∀ a, a < 16 → TFactsA a = true
  | 0, _ => tA0
  | 1, _ => tA1
  | 2, _ => tA2
  | 3, _ => tA3
  | 4, _ => tA4
  | 5, _ => tA5
  | 6, _ => tA6
  | 7, _ => tA7
  | 8, _ => tA8
  | 9, _ => tA9
  | 10, _ => tA10
  | 11, _ => tA11
  | 12, _ => tA12
  | 13, _ => tA13
  | 14, _ => tA14
  | 15, _ => tA15
  | _ + 16, h => absurd h (by omega)

end CertificateChecks.KernelTransvK
