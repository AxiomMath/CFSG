module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

noncomputable abbrev f2S (k : Nat) : Bool := CFSG.KC.LQT.P.allL (sliceK K2E (k * 192) 192) fK2

theorem f20 : f2S 0 = true := by quickRfl
theorem f21 : f2S 1 = true := by quickRfl
theorem f22 : f2S 2 = true := by quickRfl
theorem f23 : f2S 3 = true := by quickRfl
theorem f24 : f2S 4 = true := by quickRfl
theorem f25 : f2S 5 = true := by quickRfl

end CFSG.KD.LQT.C4091

end
