module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi24.Tab.F2
import Certificates.Kernel.LceSTab.Chain
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Fi24.Slices.F2W0
import CFSG.Certificates.Kernel.Fi24.Slices.F2W1
import CFSG.Certificates.Kernel.Fi24.Slices.F2W2
import CFSG.Certificates.Kernel.Fi24.Slices.F2W3
import CFSG.Certificates.Kernel.Fi24.Slices.F2W4
import CFSG.Certificates.Kernel.Fi24.Slices.F2W5
import CFSG.Certificates.Kernel.Fi24.Slices.F2W6
import CFSG.Certificates.Kernel.Fi24.Slices.F2W7
import CFSG.Certificates.Kernel.Fi24.Slices.F2W8
import CFSG.Certificates.Kernel.Fi24.Slices.F2W9
import CFSG.Certificates.Kernel.Fi24.Slices.F2C0
import CFSG.Certificates.Kernel.Fi24.Slices.F2C1
import CFSG.Certificates.Kernel.Fi24.Slices.F2C2
import CFSG.Certificates.Kernel.Fi24.Slices.F2C3
import CFSG.Certificates.Kernel.Fi24.Slices.F2C4
import CFSG.Certificates.Kernel.Fi24.Slices.F2C5
import CFSG.Certificates.Kernel.Fi24.Slices.F2C6
import CFSG.Certificates.Kernel.Fi24.Slices.F2C7

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceSeg CFSG.KD.F2

#kc_forall_tree F2okW (fun k => ∀ t < 592, CFSG.KD.F2.okW (592 * k + t) = true) 10 CFSG.KD.F2.okW_
#kc_forall_tree F2okC (fun k => ∀ t < 296, CFSG.KD.F2.okC (296 * k + t) = true) 8 CFSG.KD.F2.okC_

theorem F2facts : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 20)
    (seg JF (Nat.sub (loF (592 * 10)) (loF 0)) (loF 0)) (accF 0)) (accF (592 * 10)) = true :=
  facts_chain blk selWT INV nC (nat_lit 20) JF loF accF (592 * 10)
    (forall_of_rows (P := fun i => okW i = true) 592 10 F2okW)

theorem F2cover : Nat.beq (LceS.runCover blk LVs (nat_lit 9838242) (nat_lit 20)
    (seg JV (Nat.sub (loC (296 * 8)) (loC 0)) (loC 0)) (accC 0)) (accC (296 * 8)) = true :=
  cover_chain blk LVs (nat_lit 9838242) (nat_lit 20) JV loC accC (296 * 8)
    (forall_of_rows (P := fun i => okC i = true) 296 8 F2okC)

end CertificateChecks.KernelFi24

end
