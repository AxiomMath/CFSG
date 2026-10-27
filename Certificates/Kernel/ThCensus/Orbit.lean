module

public import Certificates.Data.Kernel.ThCensus.Defs
public import Certificates.Kernel.ThCensus.Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCensus CFSG.KD.ThCensus

theorem ch17305D :
    andB (Nat.beq (DceS.sortedCount (DceS.runSorted (fun j => PTS (Nat.add ooff j)) 8 243 osrt 1))
        243)
      (andB (Nat.beq (lenN tab) 10) (andB (Nat.beq (lenN base) 3)
        (andB (Nat.blt (base.getD 0 0) 243) (andB (Nat.blt (base.getD 1 0) 243)
          (Nat.blt (base.getD 2 0) 243))))) = true := by
  quickRfl

@[expose] noncomputable def ch17305O (k : Nat) : Bool :=
  tabOK PTS CFSG.KD.ThS.rm (RB (regAt pr k)) ooff 243 (tab.getD k [])

#kc_each ch17305O 0 10

end CertificateChecks.KernelThCensus

end
