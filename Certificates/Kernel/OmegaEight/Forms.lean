module

public import CFSG.Certificates.Kernel.O8SoundDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1
  CFSG.EvenSmallLie.OmegaEight.CPrime CFSG.EvenSmallLie.OmegaEight.Chain

@[expose] noncomputable def QP : Nat := nat_lit 10837449240524681216

@[expose] noncomputable def QM : Nat := nat_lit 11067126980204625904

theorem qBind_plus : QBind (qfB .plus) QP := by
  intro x hx
  interval_cases x <;> rfl

theorem qBind_minus : QBind (qfB .minus) QM := by
  intro x hx
  interval_cases x <;> rfl

theorem wordRows_eq (ε : Eps) : wordRows ε = wordRowsG (genRows ε) := by
  funext w
  induction w with
  | nil => rfl
  | cons s w ih => simp only [wordRows, wordRowsG, List.foldr] at ih ⊢; rw [ih]

theorem prod4_eq (ε : Eps) : prod4 ε = prod4G (genRows ε) (c0Rows ε) := by
  funext w
  induction w with
  | nil => rfl
  | cons s w ih => simp only [prod4, prod4G, List.foldr] at ih ⊢; rw [ih]; rfl

end CertificateChecks.KernelO8

end
