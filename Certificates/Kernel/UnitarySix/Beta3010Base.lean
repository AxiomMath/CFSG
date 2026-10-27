
module

public import Certificates.Kernel.UnitarySix.Struct3010Base
public import Certificates.Kernel.UnitarySix.PolarBase
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

@[expose] noncomputable def G1N : Nat := nat_lit 4029333375731133465266316549235792858047137147608942922134369139076081147909

@[expose] noncomputable def G2N : Nat := nat_lit 4248481535043882067047787218270844552694957965727465989626547830875589747264

@[expose] noncomputable def G3N : Nat := nat_lit 3788989062659729603762423655064869909684031809255659659146552634837763179584

theorem kG1 : CFSG.KC.S23.bindA G1N 6 42 CFSG.PSL3Four.Native.g₁T = true := by quickRfl
theorem kG2 : CFSG.KC.S23.bindA G2N 6 42 CFSG.PSL3Four.Native.g₂T = true := by quickRfl
theorem kG3 : CFSG.KC.S23.bindA G3N 6 42 CFSG.PSL3Four.Native.g₃T = true := by quickRfl

theorem k3010B : check3010B U.LT kWN BT G1N G2N G3N = true := by quickRfl

@[expose] noncomputable def o1WN : List Nat :=
  [22, 32, 90, 14, 91, 33, 30, 90, 2, 91, 31, 12, 90, 2, 91, 13, 30, 90, 3, 91, 31, 23]

@[expose] noncomputable def o2WN : List Nat := [22, 30, 90, 2, 91, 31]

@[expose] noncomputable def y2WN : List Nat := [0, 4, 6, 16, 18, 20, 18, 20, 18, 18, 20, 18, 18]

theorem k3010Q : check3010Q U.LT aWN kWN o1WN o2WN y2WN = true := by quickRfl

end CertificateChecks.KernelU6

end
