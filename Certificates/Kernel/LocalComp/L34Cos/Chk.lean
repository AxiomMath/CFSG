module

public import Certificates.Kernel.LocalComp.L34Cos.Defs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Cos

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB notB)

theorem kRep2005 : allN 8 (fun s => andB (Nat.beq (RQ s) (repK s))
    (andB (canonK 42 6 (mask 6) (42 * 6) (RQ s))
      (andB (canonK 42 6 (mask 6) (42 * 6) (pinvS 42 6 (mask 6) (RQ s)))
        (Nat.beq (pcomp 42 6 (mask 6) (RQ s) (pinvS 42 6 (mask 6) (RQ s))) (pidn 42 6))))) =
    true := by
  quickRfl

theorem kGI2005 : allN 6 (fun k => andB (canonK 42 6 (mask 6) (42 * 6) (GI k))
    (Nat.beq (pcomp 42 6 (mask 6) (L34R.G k) (GI k)) (pidn 42 6))) = true := by
  quickRfl

theorem kCov2005 : covC = true := by quickRfl

theorem kNeg2005 : andB (notB (notInK 20160 sT (pcomp 42 6 (mask 6)
    (pinvS 42 6 (mask 6) (RQ 0)) (RQ 0))))
    (notB (allN 120 fun j => Nat.beq (OT 1 j) (L34O.T 1 j))) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Cos

#kon_slices CertificateChecks.KernelLC.L34Cos.orbC 0 8
#kon_slices CertificateChecks.KernelLC.L34Cos.notRow 0 8

end
