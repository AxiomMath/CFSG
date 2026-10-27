module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P5
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceSeg CFSG.KD.PG10P5

theorem P5facts : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 12)
    (seg JF (Nat.sub (loF 2) (loF 0)) (loF 0)) (accF 0)) (accF 2) = true :=
  facts_chain blk selWT INV nC (nat_lit 12) JF loF accF 2 okW_all

theorem P5cover : Nat.beq (LceS.runCover blk LVs (nat_lit 3456) (nat_lit 12)
    (seg JV (Nat.sub (loC 1) (loC 0)) (loC 0)) (accC 0)) (accC 1) = true :=
  cover_chain blk LVs (nat_lit 3456) (nat_lit 12) JV loC accC 1 okC_all

end CertificateChecks.KernelPG10

end
