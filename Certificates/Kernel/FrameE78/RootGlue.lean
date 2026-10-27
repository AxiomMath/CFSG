module

public import Certificates.Kernel.FrameE78.Glue
public import Certificates.Kernel.FrameE78.RootChecks
public import CFSG.Certificates.Kernel.FrameE78.RootGlue
import CFSG.Certificates.Kernel.Spor.PK.Basic
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KD.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.FrameE78 CFSG.KC.FrameE78.Refl

private theorem tr_of7 {x : ℕ} {N : ℕ} {r : Bool}
    (h : Bool.rec (motive := fun _ => Bool) false r (Nat.blt x N) = true) : x < N ∧ r = true := by
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨bltT.1 h.1, h.2⟩

theorem root7_facts : ∀ x : Fin 7 → ZMod 3, RootP (Cm 7 C7) x := by
  have h := ch709548r7
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine root_facts (N := 1093) (k := 5) (lv := 127) (m := 63) (S := S7) (D := D7) (bs := b7)
    (cs := c7) (RR := R7) (Q := Q7) (by decide) (by decide) (by decide) (by decide) cm7_symm
    h1 h2 h3 h4 h5 ch709548p7 (fun j hj => ?_) (fun t ht => ?_) ch709548c7 (fun t ht => ?_)
    (fun t ht => ?_)
  · interval_cases j
    exacts [ch709548g7_0, ch709548g7_1, ch709548g7_2, ch709548g7_3, ch709548g7_4, ch709548g7_5,
      ch709548g7_6]
  · interval_cases t
    exacts [tr_of7 ch709548t7_0, tr_of7 ch709548t7_1, tr_of7 ch709548t7_2, tr_of7 ch709548t7_3,
      tr_of7 ch709548t7_4]
  · interval_cases t
    exacts [ch709548x7_0, ch709548x7_1, ch709548x7_2, ch709548x7_3, ch709548x7_4]
  · interval_cases t
    exacts [ch709549r_0, ch709549r_1, ch709549r_2, ch709549r_3, ch709549r_4]

end CFSG.KD.FrameE78

end
