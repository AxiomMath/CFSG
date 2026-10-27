module

public import CFSG.Monster.B.GSide.BT2BridgeDataInputs

public section

namespace CertificateChecks.KernelMonB

open CFSG.Monster.B.GSide CFSG.KC.Co2Mem

@[expose] noncomputable def codeAdjK (a b : ℕ) : Bool :=
  a != b && bWcode a b == 0 && bWcode b a == 0 && memK 2300 24 (Co2V.F 0) a &&
    memK 2300 24 (Co2V.F 0) b

theorem codeAdj_eq (a b : ℕ) : codeAdj a b = codeAdjK a b := by
  unfold codeAdj codeAdjK
  rw [vectors_contains_eq, vectors_contains_eq]

@[expose] noncomputable def codeTK (a b c : ℕ) : Bool :=
  codeAdjK a b && codeAdjK b c && codeAdjK c a && memK 2300 24 (Co2V.F 0) (a ^^^ b ^^^ c)

theorem codeT_iff (a b c : ℕ) : CodeT a b c ↔ codeTK a b c = true := by
  unfold CodeT codeTK
  rw [codeAdj_eq, codeAdj_eq, codeAdj_eq, vectors_contains_eq]
  simp only [Bool.and_eq_true, and_assoc]

@[expose] noncomputable def adjDec : DecidableRel codeGraph.Adj := fun a b =>
  decidable_of_iff (codeAdjK a b = true) (by rw [← codeAdj_eq]; rfl)

@[expose] noncomputable def codeTDec : ∀ a b c, Decidable (CodeT a b c) := fun a b c =>
  decidable_of_iff (codeTK a b c = true) (codeT_iff a b c).symm

theorem walkSteps_congr {V : Type*} [DecidableEq V] {G : SimpleGraph V} (i₁ i₂ : DecidableRel G.Adj)
    (T : V → V → V → Prop) (j₁ j₂ : ∀ x y z, Decidable (T x y z)) {u v : V} (p : G.Walk u v)
    (ss : List (WStep V)) :
    @walkSteps V _ G i₁ T j₁ u v p ss = @walkSteps V _ G i₂ T j₂ u v p ss := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  obtain rfl : j₁ = j₂ := Subsingleton.elim _ _
  rfl

end CertificateChecks.KernelMonB

end
