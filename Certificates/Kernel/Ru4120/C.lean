module

public import Certificates.Kernel.Ru4120.T
public import Certificates.Kernel.VecCert.Ru
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Ru4120

open CFSG.KC.Enum CFSG.KS.Prim CFSG.KC.VecK
open CertificateChecks.KernelVec.Ru (AT BT)

theorem canonA : canonK 4060 12 4095 48720 (TF 0) = true := by quickRfl

theorem bindA : allN 4060 (fun i => Nat.beq (pg 12 4095 (TF 0) i) (lk AT 32 i)) = true := by
  quickRfl

theorem canonB : canonK 4060 12 4095 48720 (TF 1) = true := by quickRfl

theorem bindB : allN 4060 (fun i => Nat.beq (pg 12 4095 (TF 1) i) (lk BT 32 i)) = true := by
  quickRfl

theorem valid : CFSG.QuasithinUnique.K1.SporadicPerm.slpValidAux progX 2 = true := by
  decide +kernel

theorem len : progX.length = 484 := by decide +kernel

end CFSG.KD.Ru4120

end
