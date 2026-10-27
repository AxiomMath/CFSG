module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

theorem gK15 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN (List.map (hkW 315 9) K1E)) = true := by
  quickRfl

end CFSG.KD.LQT.C4091

end
