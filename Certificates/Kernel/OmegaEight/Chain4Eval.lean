module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Data

public section

namespace CertificateChecks.KernelO8

open CFSG.EvenSmallLie.OmegaEight.Chain CFSG.EvenSmallLie.OmegaEight.Stage1

theorem z4_relCheck4_plus : relCheck4 .plus = true := by decide +kernel

theorem z4_relCheck4_minus : relCheck4 .minus = true := by decide +kernel

theorem z4_kCheck : kCheck = true := by decide +kernel

theorem z4_sqCheck : sqCheck = true := by decide +kernel

theorem z4_centerCheck_plus : centerCheck .plus = true := by decide +kernel

theorem z4_centerCheck_minus : centerCheck .minus = true := by decide +kernel

theorem cert3493 : relCheck4 .plus = true ∧ relCheck4 .minus = true ∧ kCheck = true ∧
    sqCheck = true ∧ centerCheck .plus = true ∧ centerCheck .minus = true :=
  ⟨z4_relCheck4_plus, z4_relCheck4_minus, z4_kCheck, z4_sqCheck, z4_centerCheck_plus,
    z4_centerCheck_minus⟩

end CertificateChecks.KernelO8

end
