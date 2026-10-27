module

public import Certificates.Kernel.LocalQT.SV.C4126T
public import Certificates.Kernel.LocalQT.SV.C4126D
public import Certificates.Data.Kernel.LocalQT.Nats
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.C4126

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.LQT.SP CFSG.KC.LQT.SV CFSG.KC.LQT.NP
  CFSG.QuasithinUnique.Bridge.HSExcl

theorem hT0 : headMC 3850 12 [HS.F 0, HS.F 1] [HSI 0, HSI 1] [HC.F 5] [HC.F 5] hsT0Words
    hsT0Prog T0.X T0.XI = true := by quickRfl
theorem tT0 : targMC 3850 12 2 1 hsT0Words hsT0Prog T0.X [HS.F 0, HS.F 1] = true := by quickRfl
theorem hT1 : headMC 3850 12 [HS.F 0, HS.F 1] [HSI 0, HSI 1] [HC.F 12] [HC.F 12] hsT1Words
    hsT1Prog T1.X T1.XI = true := by quickRfl
theorem tT1 : targMC 3850 12 2 1 hsT1Words hsT1Prog T1.X [HS.F 0, HS.F 1] = true := by quickRfl
theorem hT2 : headMC 3850 12 [HS.F 0, HS.F 1] [HSI 0, HSI 1] [HC.F 21] [HC.F 21] hsT2Words
    hsT2Prog T2.X T2.XI = true := by quickRfl
theorem tT2 : targMC 3850 12 2 1 hsT2Words hsT2Prog T2.X [HS.F 0, HS.F 1] = true := by quickRfl
theorem hT3 : headMC 3850 12 [HS.F 0, HS.F 1] [HSI 0, HSI 1] [HC.F 34] [HC.F 34] hsT3Words
    hsT3Prog T3.X T3.XI = true := by quickRfl
theorem tT3 : targMC 3850 12 2 1 hsT3Words hsT3Prog T3.X [HS.F 0, HS.F 1] = true := by quickRfl

theorem kT0 : Nat.ble (lenPr D0) (3 * 16) = true := by quickRfl
theorem kT1 : Nat.ble (lenPr D1) (4 * 16) = true := by quickRfl
theorem kT2 : Nat.ble (lenPr D2) (5 * 16) = true := by quickRfl
theorem kT3 : Nat.ble (lenPr D3) (4 * 16) = true := by quickRfl

theorem pP : natsOK CP.chars SY.ParL = true := by quickRfl
theorem pL : natsOK CL.chars SY.LabL = true := by quickRfl
theorem pT : natsOK CT.chars SY.TabL = true := by quickRfl
theorem bP : bindSV SY.ParL SY.PT 1024 = true := by quickRfl
theorem bL : bindSV SY.LabL SY.LT 1024 = true := by quickRfl
theorem bT : bindSV SY.TabL SY.TB (1024 * 4) = true := by quickRfl
theorem hSY : headSV 3850 12 1024 4 SY.G SY.GI = true := by quickRfl
theorem sSY : sortAllSV 1024 SY.E SY.IS SY.SR = true := by quickRfl
theorem qSY : pairsSV 12 1024 SY.E [0] 6 = true := by quickRfl

theorem gG : SY.G = [HC.F 1, HC.F 2, HC.F 3, HC.F 4] := by rfl

end CFSG.KD.LQT.C4126

end
