module

public import Certificates.Kernel.Sporadic.ONPar.DefsE
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPar

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Mathieu

theorem neg_cg : Bool.not (Nat.beq (ONPC.G 1)
    (c32 (c32 (c32 (OME.T 0) (T32E.T 1)) (OME.T 0)) (T32E.T (nget tInv 0)))) = true := by
  quickRfl

theorem neg_four : Bool.not (allN ONPC.cnt fun i => strictB (ONPC.T i) fun t =>
    bIf(Nat.beq t (pidn 32 6), true, bIf(Nat.beq t (pk 0), true,
      Nat.beq t (c32 (pk 0) (pk 1))))) = true := by
  quickRfl

theorem neg_orbit : Bool.not (penumSlK 120 7 (mask 7) 840 true ONPO.G ONPO.GI ONPO.k 314 ONPO.T
    ONPO.PL ONPO.POS ONPO.SRT ONPO.SRI 0 314) = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONPar

end
