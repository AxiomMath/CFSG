module

public import CFSG.Certificates.Kernel.Misc.O73Defs
public import Certificates.Kernel.Misc.O73Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl
import Mathlib.Tactic.IntervalCases
public import Certificates.Data.Kernel.Misc.O73
public import Mathlib

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.O73

open CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.LieType.Multipliers.O73 CFSG.YGroups
  CFSG.YGroups.ModelNative

theorem bR1 : yRels 3 2 2 = R1 := by decide +kernel
theorem bE : eWords = EW := by decide +kernel
theorem bSP : spW = SP := by decide +kernel
theorem bL : liftText = CFSG.KC.Misc.O73.strOf cL := by kernelRfl
theorem bB : betaText = CFSG.KC.Misc.O73.strOf cB := by kernelRfl
theorem bY : y322PermText = CFSG.KC.Misc.O73.strOf cY := by kernelRfl
theorem mat : matK vecList Ts Rs = true := by quickRfl
theorem relM : relMK Ts Rs R1 EW = true := by quickRfl
theorem lift : liftTextK cL LP = true := by quickRfl
theorem sp : spK LP SP = true := by quickRfl
theorem beta : betaK Rs cB cY BP YP = true := by quickRfl
theorem nEW : Nat.beq (relPK.lenLLN EW) 46 = true := by quickRfl
theorem lenL : cL.length < 2 ^ 16 := by decide +kernel
theorem lenB : cB.length < 2 ^ 16 := by decide +kernel
theorem lenY : cY.length < 2 ^ 16 := by decide +kernel
theorem nlB : 10 ∉ cB := by decide +kernel
theorem relP0 : relPK LP EW 0 1 = true := by quickRfl
theorem relP1 : relPK LP EW 1 1 = true := by quickRfl
theorem relP2 : relPK LP EW 2 1 = true := by quickRfl
theorem relP3 : relPK LP EW 3 1 = true := by quickRfl
theorem relP4 : relPK LP EW 4 1 = true := by quickRfl
theorem relP5 : relPK LP EW 5 1 = true := by quickRfl
theorem relP6 : relPK LP EW 6 1 = true := by quickRfl
theorem relP7 : relPK LP EW 7 1 = true := by quickRfl
theorem relP8 : relPK LP EW 8 1 = true := by quickRfl
theorem relP9 : relPK LP EW 9 1 = true := by quickRfl
theorem relP10 : relPK LP EW 10 1 = true := by quickRfl
theorem relP11 : relPK LP EW 11 1 = true := by quickRfl
theorem relP12 : relPK LP EW 12 1 = true := by quickRfl
theorem relP13 : relPK LP EW 13 1 = true := by quickRfl
theorem relP14 : relPK LP EW 14 1 = true := by quickRfl
theorem relP15 : relPK LP EW 15 1 = true := by quickRfl
theorem relP16 : relPK LP EW 16 1 = true := by quickRfl
theorem relP17 : relPK LP EW 17 1 = true := by quickRfl
theorem relP18 : relPK LP EW 18 1 = true := by quickRfl
theorem relP19 : relPK LP EW 19 1 = true := by quickRfl
theorem relP20 : relPK LP EW 20 1 = true := by quickRfl
theorem relP21 : relPK LP EW 21 1 = true := by quickRfl
theorem relP22 : relPK LP EW 22 1 = true := by quickRfl
theorem relP23 : relPK LP EW 23 1 = true := by quickRfl
theorem relP24 : relPK LP EW 24 1 = true := by quickRfl
theorem relP25 : relPK LP EW 25 1 = true := by quickRfl
theorem relP26 : relPK LP EW 26 1 = true := by quickRfl
theorem relP27 : relPK LP EW 27 1 = true := by quickRfl
theorem relP28 : relPK LP EW 28 1 = true := by quickRfl
theorem relP29 : relPK LP EW 29 1 = true := by quickRfl
theorem relP30 : relPK LP EW 30 1 = true := by quickRfl
theorem relP31 : relPK LP EW 31 1 = true := by quickRfl
theorem relP32 : relPK LP EW 32 1 = true := by quickRfl
theorem relP33 : relPK LP EW 33 1 = true := by quickRfl
theorem relP34 : relPK LP EW 34 1 = true := by quickRfl
theorem relP35 : relPK LP EW 35 1 = true := by quickRfl
theorem relP36 : relPK LP EW 36 1 = true := by quickRfl
theorem relP37 : relPK LP EW 37 1 = true := by quickRfl
theorem relP38 : relPK LP EW 38 1 = true := by quickRfl
theorem relP39 : relPK LP EW 39 1 = true := by quickRfl
theorem relP40 : relPK LP EW 40 1 = true := by quickRfl
theorem relP41 : relPK LP EW 41 1 = true := by quickRfl
theorem relP42 : relPK LP EW 42 1 = true := by quickRfl
theorem relP43 : relPK LP EW 43 1 = true := by quickRfl
theorem relP44 : relPK LP EW 44 1 = true := by quickRfl
theorem relP45 : relPK LP EW 45 1 = true := by quickRfl
theorem relPAll : ∀ k < 46, relPK LP EW k 1 = true := by
  intro k hk
  interval_cases k
  exacts [relP0, relP1, relP2, relP3, relP4, relP5, relP6, relP7, relP8, relP9, relP10, relP11, relP12, relP13, relP14, relP15, relP16, relP17, relP18, relP19, relP20, relP21, relP22, relP23, relP24, relP25, relP26, relP27, relP28, relP29, relP30, relP31, relP32, relP33, relP34, relP35, relP36, relP37, relP38, relP39, relP40, relP41, relP42, relP43, relP44, relP45]

end CFSG.KD.Misc.O73

end
