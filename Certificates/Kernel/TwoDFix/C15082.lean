module

public import Certificates.Kernel.TwoDFix.KQ
public import Certificates.Kernel.TwoDFix.KAlpha
public import Certificates.Kernel.TwoDFix.KBeta

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTwoDFix

open CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix

theorem rows_ok : rowsCheck = true := by decide +kernel

theorem s_ok : sCheck = true := by decide +kernel

theorem comm_ok : commCheck = true := by decide +kernel

theorem u7_ok : u7Check = true := by decide +kernel

theorem pauliK_ok : pauliK = true := by decide +kernel

open Certificates in
open CFSG in
theorem c15082 : CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.rowsCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.qCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.alphaCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.pauliCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.commCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.u7Check = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.betaCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.sCheck = true :=
  ⟨rows_ok, qCheck_of qK_ok, alphaCheck_of alphaK_ok, pauliCheck_of pauliK_ok, comm_ok, u7_ok,
    betaCheck_of betaK_ok, s_ok⟩

end CertificateChecks.KernelTwoDFix

end
