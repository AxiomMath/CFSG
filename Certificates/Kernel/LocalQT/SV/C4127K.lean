module

public import Certificates.Kernel.LocalQT.SV.C4127D
public import Certificates.Kernel.Sporadic.OddCore.J2PChain
public import Certificates.Kernel.Sporadic.OddCore.J2Cent
public import Certificates.Data.Kernel.LocalQT.J2Frob
public import Certificates.Data.Kernel.LocalQT.Nats
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kqb_range CFSG.KD.LQT.C4127.Y CFSG.KD.LQT.C4127.ckSY 0 8
#kqb_all CFSG.KD.LQT.C4127.Y CFSG.KD.LQT.C4127.ckSY 8
#kqb_range CFSG.KD.LQT.C4127.R CFSG.KD.LQT.C4127.ckRow 0 8
#kqb_all CFSG.KD.LQT.C4127.R CFSG.KD.LQT.C4127.ckRow 8
#kqb_range CFSG.KD.LQT.C4127.T CFSG.KD.LQT.C4127.ckTri 0 8
#kqb_all CFSG.KD.LQT.C4127.T CFSG.KD.LQT.C4127.ckTri 8

namespace CFSG.KD.LQT.C4127

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.LQT.SV CFSG.KC.LQT.JX CFSG.KC.LQT.NP
  CFSG.QuasithinUnique.Bridge.J2Excl CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2PC

theorem tc0 : mcP 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] [J2CentT.F 9] [J2CentT.F 9]
    j2Row0Words j2Row0Prog [J2P.S 0, J2P.S 1] = true := by quickRfl
theorem tc1 : mcP 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] [J2CentT.F 17] [J2CentT.F 17]
    j2Row1Words j2Row1Prog [J2P.S 0, J2P.S 1] = true := by quickRfl
theorem tc2 : mcP 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] [J2CentT.F 31] [J2CentT.F 31]
    j2Row2Words j2Row2Prog [J2P.S 0, J2P.S 1] = true := by quickRfl

theorem pc : pcK 315 9 256 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] SY.E j2PairData
    [J2P.S 0, J2P.S 1] = true := by quickRfl

theorem fr : frobK 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] j2FrobXWord j2FrobGWord = true := by
  quickRfl

theorem pP : natsOK CP.chars SY.ParL = true := by quickRfl
theorem pL : natsOK CL.chars SY.LabL = true := by quickRfl
theorem pT : natsOK CT.chars SY.TabL = true := by quickRfl
theorem bP : bindSV SY.ParL SY.PT 256 = true := by quickRfl
theorem bL : bindSV SY.LabL SY.LT 256 = true := by quickRfl
theorem bT : bindSV SY.TabL SY.TB (256 * 8) = true := by quickRfl
theorem hSY : headSV 315 9 256 8 SY.G SY.GI = true := by quickRfl
theorem sSY : sortAllSV 256 SY.E SY.IS SY.SR = true := by quickRfl
theorem qSY : pairsSV 9 256 SY.E [0, 1] 4 = true := by quickRfl
theorem rX : repsJX 8 256 IX.MR j2Reps = true := by quickRfl

theorem gG : SY.G = [J2CentT.F 1, J2CentT.F 2, J2CentT.F 3, J2CentT.F 4, J2CentT.F 5,
    J2CentT.F 6, J2CentT.F 7, J2CentT.F 8] := by rfl

end CFSG.KD.LQT.C4127

end
