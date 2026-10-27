module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P2
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceSeg CFSG.KD.PG10P2

theorem P2facts : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 18)
    (seg JF (Nat.sub (loF 199) (loF 0)) (loF 0)) (accF 0)) (accF 199) = true :=
  facts_chain blk selWT INV nC (nat_lit 18) JF loF accF 199 okW_all

theorem P2cover : Nat.beq (LceS.runCover blk LVs (nat_lit 321538) (nat_lit 18)
    (seg JV (Nat.sub (loC 65) (loC 0)) (loC 0)) (accC 0)) (accC 65) = true :=
  cover_chain blk LVs (nat_lit 321538) (nat_lit 18) JV loC accC 65 okC_all

end CertificateChecks.KernelPG10

end
