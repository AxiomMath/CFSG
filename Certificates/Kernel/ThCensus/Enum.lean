module

public import Certificates.Data.Kernel.ThCensus.Defs
public import Certificates.Data.Kernel.ThCensus.PermDefs
public import Certificates.Kernel.ThCensus.Data
public import Certificates.Kernel.ThCensus.PermData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCensus

open CFSG.KC.ThCensus CFSG.KD.ThCensus

@[expose] noncomputable def ch17305T (g : Nat) : Bool := permTtOK (PM 0) g (tab.getD g [])

#kc_each ch17305T 0 10

theorem ch17305E : permNfListOK reps = true := by
  quickRfl

@[expose] noncomputable def ch17305Q (b : Nat) : Bool :=
  permBlockOK (PM 0) (PM (Nat.succ b)) reps (lenN reps) (base.getD 0 0) (base.getD 1 0) (base.getD 2 0) b

#kc_each ch17305Q 0 81

end CertificateChecks.KernelThCensus

end
