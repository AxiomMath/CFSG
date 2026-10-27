module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.LyBr.Seed
public import Certificates.Data.Kernel.Spor.Bytes
public import CFSG.Certificates.Kernel.Orders.Ly.Data.Pts
public import CFSG.Certificates.Kernel.Fam.LySeed.Data.Pay
public import CFSG.Certificates.Kernel.Fam.LyAlg.Data.Pay

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy

theorem ord1_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrLy.LySeedA.chars CFSG.KD.OrdLy.P1 256 18063 = true := by
  quickRfl

theorem ord2_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrLy.LySeedB.chars CFSG.KD.OrdLy.P2 256 18063 = true := by
  quickRfl

theorem seed1_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrLy.LySeedA.chars CFSG.KD.FamLySeed.P1 256 18063 = true := by
  quickRfl

theorem seed2_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrLy.LySeedB.chars CFSG.KD.FamLySeed.P2 256 18063 = true := by
  quickRfl

theorem alg1_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrLy.LySeedA.chars CFSG.KD.FamLyAlg.P1 256 18063 = true := by
  quickRfl

theorem alg2_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrLy.LySeedB.chars CFSG.KD.FamLyAlg.P2 256 18063 = true := by
  quickRfl

end CertificateChecks.KernelLy

end
