module

public import Certificates.Data.Kernel.Spor.Fi24F4
public import Certificates.Kernel.LocalComp.Fi24TwoB.E15027
public import Certificates.Kernel.Sporadic.Fi24K.K2077
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi24F4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fi24F4 CertificateChecks.KernelSpor

@[expose] def wdD4 : List Int :=
  [1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1, 1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1,
    1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1, 1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1]

@[expose] noncomputable def Y : Nat :=
  ppow 504 9 (mask 9) (pidn 504 9)
    (wordK 504 9 (mask 9) (pidn 504 9) Fi24KC.S Fi24KC.SI [1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1]) 4

theorem yRec : recOK 504 9 (mask 9) Y Fi24KC.S Fi24KC.SI wdD4 = true := by quickRfl

theorem cnt :
    Nat.beq (cntComm 504 9 (mask 9) CertificateChecks.KernelLC.Fi24BN.T Y 0 4096) 256 = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi24F4

end
