module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1
import Certificates.Kernel.LceSTab.Chain
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W0
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W1
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W2
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W3
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W4
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W5
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W6
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W7
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W8
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1W9
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1C0
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1C1
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1C2
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1C3
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1C4
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1C5
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.P1C6

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceSeg CFSG.KD.PG10P1

#kc_forall_tree P1okW (fun k => ∀ t < 592, CFSG.KD.PG10P1.okW (592 * k + t) = true) 10
  CFSG.KD.PG10P1.okW_
#kc_forall_tree P1okC (fun k => ∀ t < 296, CFSG.KD.PG10P1.okC (296 * k + t) = true) 7
  CFSG.KD.PG10P1.okC_

theorem P1facts : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 20)
    (seg JF (Nat.sub (loF (592 * 10)) (loF 0)) (loF 0)) (accF 0)) (accF (592 * 10)) = true :=
  facts_chain blk selWT INV nC (nat_lit 20) JF loF accF (592 * 10)
    (forall_of_rows (P := fun i => okW i = true) 592 10 P1okW)

theorem P1cover : Nat.beq (LceS.runCover blk LVs (nat_lit 8696903) (nat_lit 20)
    (seg JV (Nat.sub (loC (296 * 7)) (loC 0)) (loC 0)) (accC 0)) (accC (296 * 7)) = true :=
  cover_chain blk LVs (nat_lit 8696903) (nat_lit 20) JV loC accC (296 * 7)
    (forall_of_rows (P := fun i => okC i = true) 296 7 P1okC)

end CertificateChecks.KernelPG10

end
