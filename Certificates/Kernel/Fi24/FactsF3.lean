module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi24.Slices.F3
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceSeg CFSG.KD.F3

theorem F3facts : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 18)
    (seg JF (Nat.sub (loF 313) (loF 0)) (loF 0)) (accF 0)) (accF 313) = true :=
  facts_chain blk selWT INV nC (nat_lit 18) JF loF accF 313 okW_all

theorem F3cover : Nat.beq (LceS.runCover blk LVs (nat_lit 524405) (nat_lit 18)
    (seg JV (Nat.sub (loC 67) (loC 0)) (loC 0)) (accC 0)) (accC 67) = true :=
  cover_chain blk LVs (nat_lit 524405) (nat_lit 18) JV loC accC 67 okC_all

end CertificateChecks.KernelFi24

end
