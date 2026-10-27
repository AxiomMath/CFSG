module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs
  CFSG.ComponentClassification.J2Cover

theorem kQK : CFSG.KC.LQT.P.allL Q1E (fun q => CFSG.KC.LQT.S.memL q K1E) = true := by quickRfl
theorem kAK : CFSG.KC.LQT.P.allL A2X' (fun q => CFSG.KC.LQT.S.memL q K2E) = true := by quickRfl
theorem kH : CFSG.KC.LQT.P.allL K1H (fun h => Nat.blt h 1024) = true := by quickRfl
theorem kwA :
    evalZW 315 9 (List.append S0G [t1C, t2C]) wordA = arrCodeW 9 (autStrong[0]!).toList := by
  decide +kernel
theorem kwB :
    evalZW 315 9 (List.append S0G [t1C, t2C]) wordB = arrCodeW 9 (autStrong[1]!).toList := by
  decide +kernel

end CFSG.KD.LQT.C4091

end
