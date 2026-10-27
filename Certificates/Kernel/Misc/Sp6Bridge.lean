module

public import Certificates.Kernel.Misc.Sp6
public import CFSG.Certificates.Kernel.Misc.Sp6Sound
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KD.Misc.Sp6

open CFSG.KC.Misc.Sp6 CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

theorem facts_false : pCheck false = true ∧ eaCheck false = true ∧ boundCheck false = true := by
  rw [pCheck_eq, eaCheck_eq, boundCheck_eq]
  exact sp6_sound (u := false) treeF closF invF tabsF (nc := 16)
    (by rw [Nat.eq_of_beq_eq_true lenF]; norm_num) eaF

theorem facts_true : pCheck true = true ∧ eaCheck true = true ∧ boundCheck true = true := by
  rw [pCheck_eq, eaCheck_eq, boundCheck_eq]
  exact sp6_sound (u := true) treeT closT invT tabsT (nc := 11)
    (by rw [Nat.eq_of_beq_eq_true lenT]; norm_num) eaT

theorem facts : (pCheck false = true) ∧ (pCheck true = true) ∧ (eaCheck false = true) ∧
    (eaCheck true = true) ∧ (boundCheck false = true) ∧ (boundCheck true = true) :=
  ⟨facts_false.1, facts_true.1, facts_false.2.1, facts_true.2.1, facts_false.2.2,
    facts_true.2.2⟩

end CFSG.KD.Misc.Sp6

end
