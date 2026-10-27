module

public import Certificates.Data.Kernel.ThCensus.LetDefs
public import Certificates.Kernel.ThCensus.Data
public import Certificates.Kernel.ThCensus.WordData
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCensus CFSG.KD.ThCensus CFSG.KD.ThCensusW

@[expose] noncomputable def ch17305K (j : Nat) : Bool :=
  wordLetOK 3 ((cen.getD j []).getD 1 0) (WD (Nat.add (nat_lit 50) j))

#kc_each ch17305K 0 28

theorem ch17305Z :
    andB (ord3OK RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE regZ)
      (andB (ord3OK RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE regS)
        (ord3OK RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE regU)) = true := by
  quickRfl

end CertificateChecks.KernelThCensus

end
