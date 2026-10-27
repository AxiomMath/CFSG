module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.LocalQT.SV.C4134D
public import Certificates.Kernel.LocalQT.SV.C4134S
public import Certificates.Data.Kernel.LocalQT.Nats
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.C4134

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.LQT.SP CFSG.KC.LQT.SV CFSG.KC.LQT.NP
  CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelLC.HeFix

theorem hT0 : headMC 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] [HG.F 0] [HG.F 0] heT0Words heT0Prog
    T0.X T0.XI = true := by quickRfl
theorem tT0 : targMC 8330 14 2 1 heT0Words heT0Prog T0.X [HG.F 0, HG.F 1] = true := by quickRfl
theorem hT1 : headMC 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] [PT1] [PT1] heT1Words heT1Prog
    T1.X T1.XI = true := by quickRfl
theorem tT1 : targMC 8330 14 2 1 heT1Words heT1Prog T1.X [HG.F 0, HG.F 1] = true := by quickRfl
theorem hTU : headMC 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] [PU] [PU] heUWords heUProg
    TU.X TU.XI = true := by quickRfl
theorem tTU : targMC 8330 14 2 1 heUWords heUProg TU.X [HG.F 0, HG.F 1] = true := by quickRfl
theorem hR : headRun 8330 14 [HG.F 0, HG.F 1, PU] [G0I, G1I, PU] heSylProg RS.X RS.XI = true := by
  quickRfl
theorem hSel : selRun 3 heSylProg RS.X heSylIdx SY.G = true := by quickRfl

theorem kT0 : Nat.ble (lenPr D0) (25 * 8) = true := by quickRfl
theorem kT1 : Nat.ble (lenPr D1) (23 * 8) = true := by quickRfl
theorem kTU : Nat.ble (lenPr DU) (24 * 8) = true := by quickRfl
theorem kRS : Nat.ble (lenPr DR) (26 * 8) = true := by quickRfl

theorem pP : natsOK CP.chars SY.ParL = true := by quickRfl
theorem pL : natsOK CL.chars SY.LabL = true := by quickRfl
theorem pT : natsOK CT.chars SY.TabL = true := by quickRfl
theorem bP : bindSV SY.ParL SY.PT 2048 = true := by quickRfl
theorem bL : bindSV SY.LabL SY.LT 2048 = true := by quickRfl
theorem bT : bindSV SY.TabL SY.TB (2048 * 4) = true := by quickRfl
theorem hSY : headSV 8330 14 2048 4 SY.G SY.GI = true := by quickRfl
theorem sSY : sortAllSV 2048 SY.E SY.IS SY.SR = true := by quickRfl
theorem qSY : pairsSV 14 2048 SY.E [0] 6 = true := by quickRfl

end CFSG.KD.LQT.C4134

end
