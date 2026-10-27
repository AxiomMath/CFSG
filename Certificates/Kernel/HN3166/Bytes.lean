module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.HNBr.Seed
public import Certificates.Data.Kernel.Spor.Bytes
public import CFSG.Certificates.Kernel.Orders.HN.Data.Pay
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Pay
public import CFSG.Certificates.Kernel.Fam.HNAlg.Data.Pay

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHN

theorem ord1_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrHN.HNSeedA.chars CFSG.KD.OrdHN.P1 256 17976 = true := by
  quickRfl

theorem ord2_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrHN.HNSeedB.chars CFSG.KD.OrdHN.P2 256 17976 = true := by
  quickRfl

theorem seed1_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrHN.HNSeedA.chars CFSG.KD.FamHNSeed.P1 256 17976 = true := by
  quickRfl

theorem seed2_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrHN.HNSeedB.chars CFSG.KD.FamHNSeed.P2 256 17976 = true := by
  quickRfl

theorem alg1_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrHN.HNSeedA.chars CFSG.KD.FamHNAlg.P1 256 17976 = true := by
  quickRfl

theorem alg2_bytes :
    CFSG.KS.Bytes.bytesEqK CFSG.KD.BrHN.HNSeedB.chars CFSG.KD.FamHNAlg.P2 256 17976 = true := by
  quickRfl

end CertificateChecks.KernelHN

end
