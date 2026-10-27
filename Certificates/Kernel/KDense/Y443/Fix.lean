
module

public import Certificates.Kernel.KDense.Y443.Base
public import CFSG.Certificates.Kernel.KDense.Y443.C10115All
public import CFSG.Certificates.Kernel.KDense.Y443.C10116All
public import CFSG.Certificates.Kernel.KDense.Y443.C10117All
public import CFSG.Certificates.Kernel.KDense.Y443.C10118All
public import CFSG.Certificates.Kernel.KDense.Y443.C10119All
public import CFSG.Certificates.Kernel.KDense.Y443.C10123All

public section

namespace CertificateChecks.KernelKDense.Y443

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDense.Y443 CFSG.Monster.AxisCount CFSG.YGroups.Y443

set_option maxRecDepth 100000

theorem plan10115 : planOK (words p10115) CFSG.KD.Y443.c10115.CH 72 CFSG.KD.Y443.c10115.IT = true := by
  quickRfl
theorem plan10116 : planOK (words p10116) CFSG.KD.Y443.c10116.CH 126 CFSG.KD.Y443.c10116.IT = true := by
  quickRfl
theorem plan10117 : planOK (words p10117) CFSG.KD.Y443.c10117.CH 66 CFSG.KD.Y443.c10117.IT = true := by
  quickRfl
theorem plan10118 : planOK (words p10118) CFSG.KD.Y443.c10118.CH 99 CFSG.KD.Y443.c10118.IT = true := by
  quickRfl
theorem plan10119 : planOK (words p10119) CFSG.KD.Y443.c10119.CH 108 CFSG.KD.Y443.c10119.IT = true := by
  quickRfl
theorem plan10123 : planOK (words p10123) CFSG.KD.Y443.c10123.CH 39 CFSG.KD.Y443.c10123.IT = true := by
  quickRfl

theorem lo10115 : pairsLetterOK p10115 = true := by quickRfl
theorem lo10116 : pairsLetterOK p10116 = true := by quickRfl
theorem lo10117 : pairsLetterOK p10117 = true := by quickRfl
theorem lo10118 : pairsLetterOK p10118 = true := by quickRfl
theorem lo10119 : pairsLetterOK p10119 = true := by quickRfl
theorem lo10123 : pairsLetterOK p10123 = true := by quickRfl

theorem ch10115 : ∀ k < 72, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p10115) CFSG.KD.Y443.c10115.S
    (CFSG.KD.Y443.c10115.CH k) = true := by kd_all CFSG.KD.Y443.c10115 72
theorem ch10116 : ∀ k < 126, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p10116) CFSG.KD.Y443.c10116.S
    (CFSG.KD.Y443.c10116.CH k) = true := by kd_all CFSG.KD.Y443.c10116 126
theorem ch10117 : ∀ k < 66, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p10117) CFSG.KD.Y443.c10117.S
    (CFSG.KD.Y443.c10117.CH k) = true := by kd_all CFSG.KD.Y443.c10117 66
theorem ch10118 : ∀ k < 99, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p10118) CFSG.KD.Y443.c10118.S
    (CFSG.KD.Y443.c10118.CH k) = true := by kd_all CFSG.KD.Y443.c10118 99
theorem ch10119 : ∀ k < 108, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p10119) CFSG.KD.Y443.c10119.S
    (CFSG.KD.Y443.c10119.CH k) = true := by kd_all CFSG.KD.Y443.c10119 108
theorem ch10123 : ∀ k < 39, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p10123) CFSG.KD.Y443.c10123.S
    (CFSG.KD.Y443.c10123.CH k) = true := by kd_all CFSG.KD.Y443.c10123 39

theorem hS_of {S : ℕ → St} (h0 : S 0 = CFSG.KD.KDF.I 0) (h1 : S 1 = CFSG.KD.KDF.I 1)
    (h2 : S 2 = CFSG.KD.KDF.I 2) : ∀ x < 3, S x = CFSG.KD.KDF.I x := by
  intro x hx
  interval_cases x <;> assumption

theorem c10115 : ∀ w ∈ orderWords, wordLin w = 1 :=
  rel_fix3 orderWords lo10115 plan10115 ch10115 (hS_of rfl rfl rfl) (by decide) (by decide)

theorem c10116 : ∀ w ∈ pairAWords, wordLin w = 1 :=
  rel_fix3 pairAWords lo10116 plan10116 ch10116 (hS_of rfl rfl rfl) (by decide) (by decide)

theorem c10117 : ∀ w ∈ pairBWords, wordLin w = 1 :=
  rel_fix3 pairBWords lo10117 plan10117 ch10117 (hS_of rfl rfl rfl) (by decide) (by decide)

theorem c10118 : ∀ w ∈ pairCWords, wordLin w = 1 :=
  rel_fix3 pairCWords lo10118 plan10118 ch10118 (hS_of rfl rfl rfl) (by decide) (by decide)

theorem c10119 : ∀ w ∈ pairDWords, wordLin w = 1 :=
  rel_fix3 pairDWords lo10119 plan10119 ch10119 (hS_of rfl rfl rfl) (by decide) (by decide)

theorem c10123 : wordLin spiderWord = 1 :=
  rel_fix3 [spiderWord] lo10123 plan10123 ch10123 (hS_of rfl rfl rfl) (by decide) (by decide) _
    (List.mem_singleton_self _)

end CertificateChecks.KernelKDense.Y443

end
