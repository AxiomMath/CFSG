module

public import Certificates.Data.Kernel.L34Aut
public import Certificates.Kernel.LocalComp.L34SChk

public section

namespace CertificateChecks.KernelLC.L34Aut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34K CFSG.KC.L34FixPow CFSG.KC.L34Aut
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def zP : Nat :=
  3011684680583854776274488732425914331061054085392888798784515394613085741963

@[expose] noncomputable def pinv (x : Nat) : Nat := pinvS 42 6 (mask 6) x

@[expose] noncomputable def autPt (e r1 r2 r3 r4 z z2 zr z2r a b x : Nat) : Bool :=
  andB (cenPt a b e z z2 r3 zr z2r x) (andB (expPt x)
    (andB (witPt e r1 64 L34C1.P (fun k => pinv (L34C1.P k)) false x)
      (andB (witPt e r2 168 L34C2.P (fun k => pinv (L34C2.P k)) false x)
        (andB (witPt e r3 60 L34C3.P (fun k => pinv (L34C3.P k)) (orB (Nat.beq x z) (Nat.beq x z2)) x)
          (witPt e r4 72 L34C4.P (fun k => pinv (L34C4.P k)) false x)))))

@[expose] noncomputable def aut5180 (lo n : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 0) fun r1 => strictB (RP 1) fun r2 =>
    strictB (RP 2) fun r3 => strictB (RP 3) fun r4 => strictB zP fun z =>
      strictB (pcomp 42 6 (mask 6) z z) fun z2 => strictB (pcomp 42 6 (mask 6) z r3) fun zr =>
        strictB (pcomp 42 6 (mask 6) z2 r3) fun z2r => strictB (L34C3.P 1) fun a =>
          strictB (L34C3.P 3) fun b =>
            allN n fun s => allN 1344 fun t =>
              strictB (Nat.add (Nat.mul 1344 (Nat.add lo s)) t) fun i =>
                strictB (CertificateChecks.KernelLC.L34R.T i) fun x =>
                  autPt e r1 r2 r3 r4 z z2 zr z2r a b x

@[expose] noncomputable def invsK (e m : Nat) (C : Nat → Nat) : Bool :=
  allN m fun k => andB (canonK 42 6 (mask 6) 252 (C k))
    (andB (canonK 42 6 (mask 6) 252 (pinv (C k))) (Nat.beq (pcomp 42 6 (mask 6) (C k) (pinv (C k))) e))

@[expose] noncomputable def aux5180 : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 2) fun r3 => strictB zP fun z =>
    strictB (pcomp 42 6 (mask 6) z z) fun z2 =>
      andB (Nat.beq (CertificateChecks.KernelLC.L34R.T 227642) z)
      (andB (canonK 42 6 (mask 6) 252 z) (andB (notB (Nat.beq z e)) (andB (fixPow z 3)
      (andB (Nat.beq (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) r3 z) r3) z2)
      (andB (notInK 20160 CertificateChecks.KernelLC.L34S.T z)
      (andB (notInK 20160 CertificateChecks.KernelLC.L34S.T z2)
      (andB (notInK 20160 CertificateChecks.KernelLC.L34S.T (pcomp 42 6 (mask 6) r3 z))
      (andB (notInK 20160 CertificateChecks.KernelLC.L34S.T (pcomp 42 6 (mask 6) r3 z2))
      (andB (allN 60 fun a => commPt 42 6 (L34C3.P a) z)
      (andB (allN 20160 fun k => strictB (CertificateChecks.KernelLC.L34S.T k) fun s =>
        orB (notB (commPt 42 6 s z)) (commPt 42 6 s r3))
      (andB (invsK e 64 L34C1.P) (andB (invsK e 168 L34C2.P)
      (andB (invsK e 60 L34C3.P) (invsK e 72 L34C4.P))))))))))))))

end CertificateChecks.KernelLC.L34Aut

end
