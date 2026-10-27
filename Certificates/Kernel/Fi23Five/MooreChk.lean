module

public import Certificates.Kernel.Fi23Five.ChkDefs
public import Certificates.Data.Fi24Moore

public section

namespace CFSG.KD.Fi23Five

open CFSG.KC.Fi23Five CFSG.KD.Fi23K
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative

@[expose] def mooreP : List Nat := [30317, 5884, 17218, 8258, 11568, 777]

theorem ch10137chain : chainOf (cmK G) lE 6 = mooreP := by decide +kernel

theorem ch10137nc : ∀ i < 5, cmK G mooreP[i]! mooreP[i + 1]! = false := by decide +kernel

theorem ch10137c : ∀ i < 6, ∀ j < 6, i + 2 ≤ j → cmK G mooreP[i]! mooreP[j]! = true := by
  decide +kernel

theorem ch10137sub : ∀ i < 6, mooreP[i]! ∈ lE := by decide

end CFSG.KD.Fi23Five
