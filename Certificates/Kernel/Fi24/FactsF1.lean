module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi24.Tab.F1
import Certificates.Kernel.LceSTab.Chain
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Fi24.Slices.F1W0
import CFSG.Certificates.Kernel.Fi24.Slices.F1W1
import CFSG.Certificates.Kernel.Fi24.Slices.F1W2
import CFSG.Certificates.Kernel.Fi24.Slices.F1W3
import CFSG.Certificates.Kernel.Fi24.Slices.F1W4
import CFSG.Certificates.Kernel.Fi24.Slices.F1W5
import CFSG.Certificates.Kernel.Fi24.Slices.F1W6
import CFSG.Certificates.Kernel.Fi24.Slices.F1C0
import CFSG.Certificates.Kernel.Fi24.Slices.F1C1
import CFSG.Certificates.Kernel.Fi24.Slices.F1C2
import CFSG.Certificates.Kernel.Fi24.Slices.F1C3

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceSeg CFSG.KD.F1

#kc_forall_tree F1okW (fun k => ∀ t < 592, CFSG.KD.F1.okW (592 * k + t) = true) 7 CFSG.KD.F1.okW_
#kc_forall_tree F1okC (fun k => ∀ t < 296, CFSG.KD.F1.okC (296 * k + t) = true) 4 CFSG.KD.F1.okC_

theorem F1facts : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 24)
    (seg JF (Nat.sub (loF (592 * 7)) (loF 0)) (loF 0)) (accF 0)) (accF (592 * 7)) = true :=
  facts_chain blk selWT INV nC (nat_lit 24) JF loF accF (592 * 7)
    (forall_of_rows (P := fun i => okW i = true) 592 7 F1okW)

theorem F1cover : Nat.beq (LceS.runCover blk LVs (nat_lit 6653548) (nat_lit 24)
    (seg JV (Nat.sub (loC (296 * 4)) (loC 0)) (loC 0)) (accC 0)) (accC (296 * 4)) = true :=
  cover_chain blk LVs (nat_lit 6653548) (nat_lit 24) JV loC accC (296 * 4)
    (forall_of_rows (P := fun i => okC i = true) 296 4 F1okC)

end CertificateChecks.KernelFi24

end
