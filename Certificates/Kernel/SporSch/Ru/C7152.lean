module

public import Certificates.Kernel.SporSch.Ru.C7152D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuU1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuB1K CertificateChecks.KernelSporSch.RuLines
  CertificateChecks.KernelSporSch.RuCt

@[expose] noncomputable def cmz (G X : Nat) : Bool :=
  strictB (qc G X) (fun p => strictB (qc X G) (fun q =>
    bIf(Nat.beq p q, true, Nat.beq p (qc RuF.ZF q))))

@[expose] noncomputable def u1pK (G : Nat) : Bool :=
  bIf(allN 6 (fun j => cmz G (RuT1920.L (Nat.add 24 j))), anyK 32 (fun i => Nat.beq G (UF i)), true)

@[expose] noncomputable def scr1 (T0 T X x : Nat) : Bool :=
  strictB (pg 11 (mask 11) T0 (pg 11 (mask 11) T (pg 11 (mask 11) X x))) (fun a =>
  strictB (pg 11 (mask 11) X (pg 11 (mask 11) T0 (pg 11 (mask 11) T x))) (fun b =>
    bIf(Nat.beq a b, false, bIf(Nat.beq a (pg 11 (mask 11) RuF.ZF b), false, true))))

@[expose] noncomputable def scr (T0 T : Nat) : Bool :=
  anyK 6 (fun j => anyK 3 (fun x => scr1 T0 T (RuT1920.L (Nat.add 24 j)) x))

@[expose] noncomputable def u1RowG (LR TR : Nat → Nat) (a : Nat) : Bool :=
  strictB (LR (nat_lit 0)) (fun R0 => strictB (LR (nat_lit 1)) (fun R1 =>
  strictB (TR (Nat.add (roff 1920 (1920 * 11) R0) a)) (fun T0 =>
  strictB (roff 1920 (1920 * 11) R1) (fun o1 =>
    allN (rcnt R1) (fun b => strictB (TR (Nat.add o1 b)) (fun T =>
      bIf(scr T0 T, true, u1pK (pcomp 1920 11 (mask 11) T0 T))))))))

@[expose] noncomputable def u1Row (a : Nat) : Bool := u1RowG RuSS2.LR RuSS2.TR a

theorem ch7152cnt : Nat.beq (rcnt (RuSS2.LR 0)) 1024 = true := by quickRfl

theorem ch7152negR : (!bIf(allN 0 (fun j => cmz (RuT1920.L 7) (RuT1920.L (Nat.add 24 j))),
    anyK 32 (fun i => Nat.beq (RuT1920.L 7) (UF i)), true)) = true := by quickRfl

theorem ch7152negS : (!scr (pidn 1920 11) (pidn 1920 11)) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuU1

#kss_each CertificateChecks.KernelSporSch.RuU1.ch7152R CertificateChecks.KernelSporSch.RuU1.u1Row 1024

end
