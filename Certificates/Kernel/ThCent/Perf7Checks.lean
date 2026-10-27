module

public import Certificates.Kernel.ThCent.LDefs
public import Certificates.Data.Kernel.ThCent.Perf7

public section

namespace CFSG.KD.ThCent.L

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenPerfect

theorem perf7_inv39 : Nat.beq (mulB ThS.c ThS.rm (V7 39) (V7 31)) ThS.ONE = true := by
  decide +kernel

theorem perf7_inv40 : Nat.beq (mulB ThS.c ThS.rm (V7 40) (V7 34)) ThS.ONE = true := by
  decide +kernel

theorem perf7_s0 : neB ThS.c ThS.rm ThS.ONE (wordR ThS.c ThS.rm ThS.ONE V7 sWords[0]!) ThS.ONE =
    true := by
  decide +kernel

theorem perf7_0 : perf7At ThS.c ThS.rm ThS.ONE V7 W.Z7 0 = true := by decide +kernel
theorem perf7_1 : perf7At ThS.c ThS.rm ThS.ONE V7 W.Z7 1 = true := by decide +kernel
theorem perf7_2 : perf7At ThS.c ThS.rm ThS.ONE V7 W.Z7 2 = true := by decide +kernel
theorem perf7_3 : perf7At ThS.c ThS.rm ThS.ONE V7 W.Z7 3 = true := by decide +kernel
theorem perf7_4 : perf7At ThS.c ThS.rm ThS.ONE V7 W.Z7 4 = true := by decide +kernel
theorem perf7_5 : perf7At ThS.c ThS.rm ThS.ONE V7 W.Z7 5 = true := by decide +kernel

end CFSG.KD.ThCent.L
