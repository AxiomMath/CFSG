module

public import CFSG.Certificates.Kernel.LocalQTSixSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4051

open CFSG.KC.LQT.X6 CFSG.KC.LQT.S CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def C0 : List Nat := [139463745, 139558946]
@[expose] def Ca : List Nat := [139463745, 139558946, 139529248]
@[expose] def Cb : List Nat := [139463745, 139558946, 101877888]
@[expose] def CR : List Nat :=
  [170919972, 168919170, 38899714, 68161699, 36770944, 35782819]

theorem h0 : d0Gens.map code = C0 := by decide +kernel
theorem ha : saGens.map code = Ca := by decide +kernel
theorem hb : sbGens.map code = Cb := by decide +kernel
theorem hr : repsP.map code = CR := by decide +kernel
theorem hk : c4051 C0 Ca Cb CR 4 5 5 11 8 24 24 = true := by quickRfl

end CFSG.KD.LQT.C4051

end
