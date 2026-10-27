module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P4
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceSeg CFSG.KD.PG10P4

theorem P4facts : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 14)
    (seg JF (Nat.sub (loF 1) (loF 0)) (loF 0)) (accF 0)) (accF 1) = true :=
  facts_chain blk selWT INV nC (nat_lit 14) JF loF accF 1 okW_all

theorem P4cover : Nat.beq (LceS.runCover blk LVs (nat_lit 7) (nat_lit 14)
    (seg JV (Nat.sub (loC 1) (loC 0)) (loC 0)) (accC 0)) (accC 1) = true :=
  cover_chain blk LVs (nat_lit 7) (nat_lit 14) JV loC accC 1 okC_all

end CertificateChecks.KernelPG10

end
