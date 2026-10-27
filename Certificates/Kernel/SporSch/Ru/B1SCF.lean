module

public import Certificates.Kernel.SporSch.Ru.B1SC
public import Certificates.Kernel.SporSch.Ru.B1EF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.RuB1 CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def cPts : List Nat := [509, 1531, 2539, 3557]

@[expose] noncomputable def cmPt (G X : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih =>
    bAnd(Nat.beq (pg 12 (mask 12) G (pg 12 (mask 12) X x))
      (pg 12 (mask 12) X (pg 12 (mask 12) G x)), ih)) l

@[expose] noncomputable def cmF (G X : Nat) : Bool := bAnd(cmPt G X cPts, cm4 G X)

@[expose] noncomputable def scpG (G : Nat) : Bool :=
  bIf(Nat.beq (pc G G) (pidn 4060 12),
    bIf(allN 7 (fun j => cmF G (EA j)), true,
      anyK 12 (fun k => allN 7 (fun i => cmF G (SE (Nat.add (Nat.mul 7 k) i))))), true)

@[expose] noncomputable def scpF (T0 T1 : Nat) : Bool :=
  bIf(sqAll T0 T1 sqPts, strictB (pcomp 4060 12 (mask 12) T0 T1) (fun G => scpG G), true)

@[expose] noncomputable def scrowF (a : Nat) : Bool :=
  strictB (RuS4.LR (nat_lit 0)) (fun R0 => strictB (RuS4.LR (nat_lit 1)) (fun R1 =>
  strictB (RuS4.TR (Nat.add (roff 4060 (4060 * 12) R0) a)) (fun T0 =>
  strictB (roff 4060 (4060 * 12) R1) (fun o1 =>
    allN (rcnt R1) (fun b => strictB (RuS4.TR (Nat.add o1 b)) (fun T1 => scpF T0 T1))))))

end CertificateChecks.KernelSporSch.RuB1K

end
