module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData

public section

namespace CertificateChecks.KernelO8

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.CPrime

theorem cp_reflRows_plus : reflRowsCheck .plus = true := by decide +kernel

theorem cp_reflRows_minus : reflRowsCheck .minus = true := by decide +kernel

theorem cp_reflQf_plus : reflQfCheck .plus = true := by decide +kernel

theorem cp_reflQf_minus : reflQfCheck .minus = true := by decide +kernel

theorem cp_sigma_plus : sigmaCheck .plus = true := by decide +kernel

theorem cp_sigma_minus : sigmaCheck .minus = true := by decide +kernel

theorem cp_transN_plus : transNCheck .plus = true := by decide +kernel

theorem cp_transN_minus : transNCheck .minus = true := by decide +kernel

theorem cp_sum_plus : sumCheck .plus = true := by decide +kernel

theorem cp_sum_minus : sumCheck .minus = true := by decide +kernel

theorem cp_order3 : order3Check = true := by decide +kernel

theorem cert3530 : reflRowsCheck .plus = true ∧ reflRowsCheck .minus = true ∧
    reflQfCheck .plus = true ∧ reflQfCheck .minus = true ∧ sigmaCheck .plus = true ∧
    sigmaCheck .minus = true ∧ transNCheck .plus = true ∧ transNCheck .minus = true ∧
    sumCheck .plus = true ∧ sumCheck .minus = true ∧ order3Check = true :=
  ⟨cp_reflRows_plus, cp_reflRows_minus, cp_reflQf_plus, cp_reflQf_minus, cp_sigma_plus,
    cp_sigma_minus, cp_transN_plus, cp_transN_minus, cp_sum_plus, cp_sum_minus, cp_order3⟩

end CertificateChecks.KernelO8

end
