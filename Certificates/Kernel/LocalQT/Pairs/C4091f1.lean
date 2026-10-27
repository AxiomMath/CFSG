module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

noncomputable abbrev f1S (k : Nat) : Bool :=
  zipN (sliceK K1E (k * 240) 240) (sliceK K1H (k * 240) 240) fK1

theorem f10 : f1S 0 = true := by quickRfl
theorem f11 : f1S 1 = true := by quickRfl
theorem f12 : f1S 2 = true := by quickRfl
theorem f13 : f1S 3 = true := by quickRfl

end CFSG.KD.LQT.C4091

end
