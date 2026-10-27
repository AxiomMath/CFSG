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

theorem ch17305G : andB (Nat.beq nb 7) (blocksOK bl nb 10) = true := by quickRfl

@[expose] noncomputable def ch17305B (b : Nat) : Bool :=
  blockOK RB PTS CFSG.KD.ThS.rm pr 10 bl b (boff.getD b 0) (btree.getD b []) (bsrt.getD b [])

#kc_each ch17305B 0 7

end CertificateChecks.KernelThCensus

end
