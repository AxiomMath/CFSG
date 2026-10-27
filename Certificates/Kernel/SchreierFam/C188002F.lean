module

public import Certificates.Data.HuppertU38.Model

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSchreierFam.U38

open CFSG.RankThree.PartTwo.Sec4.Item434U38 GF64

theorem nAddAssoc : (List.range 64).all (fun x => (List.range 64).all fun y =>
    (List.range 64).all fun z => (((x ^^^ y) % 64) ^^^ z) % 64 == (x ^^^ ((y ^^^ z) % 64)) % 64) =
    true := by
  decide +kernel

theorem nMulAssoc : (List.range 64).all (fun x => (List.range 64).all fun y =>
    (List.range 64).all fun z =>
      mulNat (mulNat x y % 64) z % 64 == mulNat x (mulNat y z % 64) % 64) = true := by
  decide +kernel

theorem nDistrib : (List.range 64).all (fun x => (List.range 64).all fun y =>
    (List.range 64).all fun z =>
      mulNat x ((y ^^^ z) % 64) % 64 == ((mulNat x y % 64) ^^^ (mulNat x z % 64)) % 64) = true := by
  decide +kernel

theorem small : (∀ a : GF64, 0 + a = a) ∧ (∀ a : GF64, -a + a = 0) ∧
    (∀ a b : GF64, a * b = b * a) ∧ (∀ a : GF64, 1 * a = a) ∧
    (∀ a : GF64, a ≠ 0 → a * a⁻¹ = 1) ∧ ((0 : GF64)⁻¹ = 0) ∧ (∃ a b : GF64, a ≠ b) := by
  decide +kernel

theorem rootsSU : (∀ k : Fin 6, rootB k + (rootB k).conj8 + rootA k * (rootA k).conj8 = 0) ∧
    ∀ k : Fin 7, SpecialUnitaryM (genMat k) := by
  decide +kernel

end CertificateChecks.KernelSchreierFam.U38
