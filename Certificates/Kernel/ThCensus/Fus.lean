module

public import Certificates.Kernel.ThCensus.WordChecks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCensus CFSG.KD.ThCensus CFSG.KD.ThCensusW

theorem ch17305I :
    andB (Nat.beq (lenN reps) 56) (andB (Nat.beq (lenN tgts) 28) (andB (nfsOK reps)
      (andB (nfsOK tgts) (andB (Nat.beq (lenN fus) 50) (andB (fusIdxOK 56 28 fus)
        (andB (Nat.beq (lenN cen) 28) (coverOK reps tgts fus 56))))))) = true := by
  quickRfl

#kc_each ch17305F 0 50

end CertificateChecks.KernelThCensus

end
