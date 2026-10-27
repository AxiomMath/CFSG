module

public import Certificates.Data.Kernel.PermCent.U43QuatRelW

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43.Quat
  CFSG.LieType.Multipliers.U43 Matrix

theorem quat_rels :
    ((matK cS01).map (· ^ 3))ᵀ * matK cS01 = 1 ∧ (matK cS01).det = uncode 3 ∧
      ((matK cY0).map (· ^ 3))ᵀ * matK cY0 = 1 ∧ (matK cY0).det = uncode 3 ∧
      matK (qc 0) * matK (qc 0) = 1 ∧ matK (qc 2) * matK (qc 2) = matK (qc 0) ∧
      matK (qc 1) * matK (qc 2) * matK (qc 1) = matK (qc 2) ∧
      matK (qc 3) * matK (qc 4) * matK (qc 3) = matK (qc 4) ∧
      matK (qc 5) * matK (qc 1) = matK (qc 1) * matK (qc 5) ∧
      matK (qc 5) * matK (qc 2) = matK (qc 2) * matK (qc 5) ∧
      matK cS01 * matK cS01 = 1 ∧
      matK cS01 * matK (qc 3) = matK (qc 1) * matK cS01 ∧
      matK cS01 * matK (qc 4) = matK (qc 2) * matK cS01 ∧
      matK cS01 * matK (qc 1) = matK (qc 3) * matK cS01 ∧
      matK cS01 * matK (qc 2) = matK (qc 4) * matK cS01 ∧
      matK cS01 * matK (qc 0) = (-1 : F9) • (matK (qc 0) * matK cS01) ∧
      matK (qc 7) * matK (qc 0) = (-1 : F9) • (matK (qc 0) * matK (qc 7)) ∧
      matK cY0 * (matK cY0 * matK cY0) = 1 ∧
      matK cY0 * matK (qc 5) = matK (qc 5) * matK cY0 ∧
      matK cY0 * matK (qc 1) = matK (qc 2) * matK cY0 ∧
      matK cY0 * matK (qc 2) = matK (qc 1) * matK (qc 2) * matK cY0 ∧
      matK (qc 8) * matK (qc 2) = matK (qc 2) * matK (qc 0) * matK (qc 8) ∧
      matK (qc 9) * matK (qc 2) = matK (qc 2) * matK (qc 9) ∧
      matK (qc 10) * matK (qc 2) = matK (qc 1) * matK (qc 2) * matK (qc 0) * matK (qc 10) ∧
      matK (qc 11) * matK (qc 2) = matK (qc 1) * matK (qc 2) * matK (qc 11) ∧
      matK (qc 12) * matK (qc 2) = matK (qc 2) * matK (qc 12) ∧
      matK (qc 13) * matK (qc 2) = matK (qc 2) * matK (qc 0) * matK (qc 13) := by
  decide +kernel

theorem quat_rels_gam : (List.range 6).all (fun j =>
    decide (matK (qc (8 + j)) * matK (qc 1) = matK (qc 1) * matK (qc 0) * matK (qc (8 + j)))) =
      true := by
  decide +kernel

theorem quat_rels_ne : ((List.range 820).any (fun i => !Nat.beq (imgK (qc 0) false i) i) &&
    (List.range 820).any (fun i => !Nat.beq (imgK (qc 5) false (imgK (qc 4) false i))
      (imgK (qc 4) false (imgK (qc 5) false i))) &&
    (List.range 820).any (fun i => !Nat.beq (imgK cY0 false (imgK (qc 1) false i))
      (imgK (qc 1) false (imgK cY0 false i)))) = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
