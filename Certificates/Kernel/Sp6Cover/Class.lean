module

public import Certificates.Kernel.Sp6Cover.YChain
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulH
meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.PhilipHallSp6Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSp6Cover

meta def dM : Array (Array Nat) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData.yS.extract 0 3

meta def diM : Array (Array Nat) := dM.map (CFSG.KS.RawGen.inv 240)

meta def tM : Array Nat := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData.tA

end CertificateChecks.KernelSp6Cover

#kmulh CertificateChecks.KernelSp6Cover.TC 240 8 CertificateChecks.KernelSp6Cover.dM
  CertificateChecks.KernelSp6Cover.diM CertificateChecks.KernelSp6Cover.tM 630

namespace CertificateChecks.KernelSp6Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem tcGens : bAnd(allN 3 (fun j => bAnd(Nat.beq (TC.G j) (YC.S j),
      Nat.beq (TC.GI j) (YC.SI j))),
    bAnd(allN 3 (fun j => bAnd(canonK 240 8 (mask 8) (240 * 8) (TC.G j),
      canonK 240 8 (mask 8) (240 * 8) (TC.GI j))),
    bAnd(canonK 240 8 (mask 8) (240 * 8) TC.R, szOK 240 8))) = true := by
  quickRfl

theorem tcRoot : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData.tA =
    unpack 240 8 TC.R := by
  decide +kernel

theorem tcCnt : Nat.beq TC.cnt 630 = true := by quickRfl

theorem tcHd : penumHdK TC.R TC.cnt 630 TC.T TC.PL = true := by quickRfl

theorem tcE0 : penumSlK 240 8 (mask 8) (240 * 8) true TC.G TC.GI 3 TC.cnt TC.T TC.PL TC.POS
    TC.SRT TC.SRI 0 210 = true := by quickRfl

theorem tcE1 : penumSlK 240 8 (mask 8) (240 * 8) true TC.G TC.GI 3 TC.cnt TC.T TC.PL TC.POS
    TC.SRT TC.SRI 210 210 = true := by quickRfl

theorem tcE2 : penumSlK 240 8 (mask 8) (240 * 8) true TC.G TC.GI 3 TC.cnt TC.T TC.PL TC.POS
    TC.SRT TC.SRI 420 210 = true := by quickRfl

theorem tcH : slK TC.cnt (hsortPtK 240 8 (mask 8) TC.cnt TC.T TC.HS TC.HSI) 0 TC.cnt = true := by
  quickRfl

end CertificateChecks.KernelSp6Cover

end
