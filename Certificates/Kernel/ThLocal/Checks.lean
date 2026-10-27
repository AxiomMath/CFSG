module

public import Certificates.Data.Kernel.ThLocal.Defs
public import Certificates.Kernel.ThLocal.Data
public import Certificates.Kernel.ThCensus.Data
public import Certificates.Kernel.ThCensus.PermData
public import Certificates.Kernel.ThCensus.WordData
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThLocal

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCensus CFSG.KC.ThLocal CFSG.KD.ThCensus
  CFSG.KD.ThCensusW CFSG.KD.ThLocal

@[expose] noncomputable def ch13650T (j : Nat) : Bool :=
  tgtLocOK (PM 0) (base.getD 0 0) (base.getD 1 0) (base.getD 2 0) reps tgts fus j (tc.getD j [])
    (te.getD j [])

#kc_each ch13650T 0 28

theorem ch13650Z :
    andB (zcOK (PM 0) (base.getD 0 0) (base.getD 1 0) (base.getD 2 0))
      (Nat.beq regZ (regAt pr 9)) = true := by
  quickRfl

theorem ch13650V :
    invOK RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE regX1 regX2 regZ invn invw = true := by
  quickRfl

end CertificateChecks.KernelThLocal

end
