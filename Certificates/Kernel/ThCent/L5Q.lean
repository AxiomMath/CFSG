module

public import Certificates.Kernel.ThCent.LDefs

public section

namespace CFSG.KD.ThCent.L

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent

theorem ch5q_strictF (y : Nat) (k : Nat → Bool) : strictF y k = k y := by
  cases y <;> rfl

theorem chunkOK_add {α : Type} (f : α → Bool) (E : List α) (lo a b : Nat) :
    chunkOK f E lo (a + b) = (chunkOK f E lo a && chunkOK f E (lo + a) b) := by
  simp only [chunkOK, List.take_add, List.all_append, List.drop_drop]

@[expose] noncomputable def ch5q (i : Nat) : Bool := strictF C5 fun C =>
  chunkOK (eltRec ThS.c ThS.rm ThS.ONE V5 C 24) L5.E (i * 10) 10

theorem ch5_of_q (k : Nat) (h0 : ch5q (5 * k) = true) (h1 : ch5q (5 * k + 1) = true)
    (h2 : ch5q (5 * k + 2) = true) (h3 : ch5q (5 * k + 3) = true)
    (h4 : ch5q (5 * k + 4) = true) : ch5 k = true := by
  simp only [ch5q, ch5q_strictF] at h0 h1 h2 h3 h4
  have e : (50 : Nat) = 10 + (10 + (10 + (10 + 10))) := rfl
  rw [ch5, ch5q_strictF, e]
  simp only [chunkOK_add, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rwa [(by omega : 5 * k * 10 = k * 50)] at h0
  · rwa [(by omega : (5 * k + 1) * 10 = k * 50 + 10)] at h1
  · rwa [(by omega : (5 * k + 2) * 10 = k * 50 + 10 + 10)] at h2
  · rwa [(by omega : (5 * k + 3) * 10 = k * 50 + 10 + 10 + 10)] at h3
  · rwa [(by omega : (5 * k + 4) * 10 = k * 50 + 10 + 10 + 10 + 10)] at h4

end CFSG.KD.ThCent.L

end
