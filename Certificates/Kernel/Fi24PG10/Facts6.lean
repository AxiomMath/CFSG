module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P6
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceSeg CFSG.KD.PG10P6

theorem P6facts : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 10)
    (seg JF (Nat.sub (loF 6) (loF 0)) (loF 0)) (accF 0)) (accF 6) = true :=
  facts_chain blk selWT INV nC (nat_lit 10) JF loF accF 6 okW_all

theorem P6cover : Nat.beq (LceS.runCover blk LVs (nat_lit 12600) (nat_lit 10)
    (seg JV (Nat.sub (loC 4) (loC 0)) (loC 0)) (accC 0)) (accC 4) = true :=
  cover_chain blk LVs (nat_lit 12600) (nat_lit 10) JV loC accC 4 okC_all

end CertificateChecks.KernelPG10

end
