module

public import Certificates.Kernel.FrameE78.Checks
public import CFSG.Certificates.Kernel.FrameE78.Glue
import CFSG.Certificates.Kernel.Spor.PK.Basic
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KD.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.FrameE78 CFSG.KC.FrameE78.Refl

private theorem sym7 : ∀ i < 7, ∀ j < 7, cij C7 j i = cij C7 i j := by decide +kernel

private theorem sym8 : ∀ i < 8, ∀ j < 8, cij C8 j i = cij C8 i j := by decide +kernel

theorem cm7_symm : (Cm 7 C7).IsSymm :=
  Matrix.IsSymm.ext fun i j => congrArg (fun z : ℕ => (z : ZMod 3)) (sym7 i i.isLt j j.isLt)

theorem cm8_symm : (Cm 8 C8).IsSymm :=
  Matrix.IsSymm.ext fun i j => congrArg (fun z : ℕ => (z : ZMod 3)) (sym8 i i.isLt j j.isLt)

private theorem tr_of {x : ℕ} {N : ℕ} {r : Bool}
    (h : Bool.rec (motive := fun _ => Bool) false r (Nat.blt x N) = true) : x < N ∧ r = true := by
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨bltT.1 h.1, h.2⟩

theorem frame7_facts :
    (∀ r t, ConjDer (sS (Cm 7 C7)) r → ConjDer (sS (Cm 7 C7)) t →
      r = t ∨ r * t = t * r ∨ r * t * r = t * r * t) ∧
    ∀ x : Fin 7 → ZMod 3, x ≠ 0 → Dich (AlwP 7) (fixSet (Cm 7 C7) x) := by
  have h := ch709548r7
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine frame_facts (N := 1093) (k := 5) (lv := 127) (m := 63) (S := S7) (D := D7) (bs := b7)
    (cs := c7) (RR := R7) (Q := Q7) (by decide) (by decide) cm7_symm
    h1 h2 h3 h4 h5 ch709548p7 (fun j hj => ?_) (fun t ht => ?_) ch709548c7 (fun t ht => ?_)
  · interval_cases j
    exacts [ch709548g7_0, ch709548g7_1, ch709548g7_2, ch709548g7_3, ch709548g7_4, ch709548g7_5,
      ch709548g7_6]
  · interval_cases t
    exacts [tr_of ch709548t7_0, tr_of ch709548t7_1, tr_of ch709548t7_2, tr_of ch709548t7_3,
      tr_of ch709548t7_4]
  · interval_cases t
    exacts [ch709548x7_0, ch709548x7_1, ch709548x7_2, ch709548x7_3, ch709548x7_4]

theorem frame8_facts :
    (∀ r t, ConjDer (sS (Cm 8 C8)) r → ConjDer (sS (Cm 8 C8)) t →
      r = t ∨ r * t = t * r ∨ r * t * r = t * r * t) ∧
    ∀ x : Fin 8 → ZMod 3, x ≠ 0 → Dich (AlwP 8) (fixSet (Cm 8 C8) x) := by
  have h := ch709548r8
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine frame_facts (N := 3280) (k := 4) (lv := 255) (m := 120) (S := S8) (D := D8) (bs := b8)
    (cs := c8) (RR := R8) (Q := Q8) (by decide) (by decide) cm8_symm
    h1 h2 h3 h4 h5 ch709548p8 (fun j hj => ?_) (fun t ht => ?_) ch709548c8 (fun t ht => ?_)
  · interval_cases j
    exacts [ch709548g8_0, ch709548g8_1, ch709548g8_2, ch709548g8_3, ch709548g8_4, ch709548g8_5,
      ch709548g8_6, ch709548g8_7]
  · interval_cases t
    exacts [tr_of ch709548t8_0, tr_of ch709548t8_1, tr_of ch709548t8_2, tr_of ch709548t8_3]
  · interval_cases t
    exacts [ch709548x8_0, ch709548x8_1, ch709548x8_2, ch709548x8_3]

end CFSG.KD.FrameE78

end
