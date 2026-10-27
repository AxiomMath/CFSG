module

public import CFSG.Open.LocalVocabulary
public import Certificates.Data.Kernel.L34Pow
public import Certificates.Data.Kernel.L34Scan
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34SData

public section

namespace CertificateChecks.KernelLC.L34T3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KC.L34Scan2 CFSG.KC.L34Pow CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def wK (x xi s si : Nat) : Nat :=
  pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) xi
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) si x) s) xi)) x)
    (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) x si) xi) s)

@[expose] noncomputable def witU (e x xi : Nat) : Bool :=
  notB (allN 72 fun a => strictB (L34C4.P a) fun s =>
    notB (andB (Nat.beq (ppowK s 8) e) (strictB (ppowK s 7) fun si =>
      notB (memL 9 L34D2.P (wK x xi s si)))))

@[expose] noncomputable def unitPt (r e x : Nat) : Bool :=
  orB (notB (commPt 42 6 x r)) (orB (memL 72 L34C4.P x)
    (orB (notB (with945 x fun y => Nat.beq y e)) (with944 x (witU e x))))

@[expose] noncomputable def unit23230 (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 3) fun r => scanSl (unitPt r e) L34R.T 1344 s

end CertificateChecks.KernelLC.L34T3

end
