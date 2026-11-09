module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Data

public section

namespace CertificateChecks.KernelO8

open CFSG.EvenSmallLie.OmegaEight.Chain CFSG.EvenSmallLie.OmegaEight.Stage1

theorem z4_relCheck4_plus : relCheck4 .plus = true := by decide +kernel

theorem z4_relCheck4_minus : relCheck4 .minus = true := by decide +kernel

theorem z4_kCheck : kCheck = true := by decide +kernel

@[expose] def mv4F (A : Array (Array ℕ)) (v : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 6) fun i =>
    (m4Get A i (0 : Fin 6) * v.getD ((0 : Fin 6) : ℕ) 0 +
      m4Get A i (1 : Fin 6) * v.getD ((1 : Fin 6) : ℕ) 0 +
      m4Get A i (2 : Fin 6) * v.getD ((2 : Fin 6) : ℕ) 0 +
      m4Get A i (3 : Fin 6) * v.getD ((3 : Fin 6) : ℕ) 0 +
      m4Get A i (4 : Fin 6) * v.getD ((4 : Fin 6) : ℕ) 0 +
      m4Get A i (5 : Fin 6) * v.getD ((5 : Fin 6) : ℕ) 0) % 4

theorem mv4_eq : mv4 = mv4F := by
  funext A v
  simp only [mv4, mv4F, Fin.sum_univ_six]

theorem z4_sqCheck : sqCheck = true := by
  simp only [sqCheck, mv4_eq]
  decide +kernel

theorem z4_centerCheck_plus : centerCheck .plus = true := by decide +kernel

theorem z4_centerCheck_minus : centerCheck .minus = true := by decide +kernel

theorem cert3493 : relCheck4 .plus = true ∧ relCheck4 .minus = true ∧ kCheck = true ∧
    sqCheck = true ∧ centerCheck .plus = true ∧ centerCheck .minus = true :=
  ⟨z4_relCheck4_plus, z4_relCheck4_minus, z4_kCheck, z4_sqCheck, z4_centerCheck_plus,
    z4_centerCheck_minus⟩

end CertificateChecks.KernelO8

end
