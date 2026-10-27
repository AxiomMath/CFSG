module

public import Certificates.Kernel.LocalComp.L34V1.Data
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Data.Kernel.L34Scan
public import Certificates.Data.Kernel.L34Pre
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CertificateChecks.KernelLC.L34V1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CertificateChecks.KernelLC.L34V1G
open CFSG.KLie.CT (fget andB orB notB)

@[expose] noncomputable def pc (x y : Nat) : Nat := pcomp 42 6 (mask 6) x y

@[expose] noncomputable def pc16 (x y : Nat) : Nat := pcomp 16 5 (mask 5) x y

@[expose] noncomputable def yg (y i : Nat) : Nat := pg 5 (mask 5) (YP y) i

@[expose] noncomputable def W (k : Nat) : Nat :=
  fget (WP (Nat.shiftRight k (nat_lit 4))) (Nat.land k (nat_lit 15)) (nat_lit 9)

@[expose] noncomputable def inFE (x : Nat) : Bool :=
  notB (allN 16 fun q => notB (Nat.beq (FE.T q) x))

@[expose] noncomputable def vK (e k t : Nat) : Bool :=
  strictB (pinvS 42 6 (mask 6) t) fun ti =>
    andB (canonK 42 6 (mask 6) (42 * 6) ti) (andB (Nat.beq (pc t ti) e)
      (orB (notB (allN 16 fun i => inFE (pc (pc t (FE.T i)) ti)))
        (strictB (W k) fun y => andB (Nat.blt y 360)
          (allN 16 fun i => strictB (yg y i) fun p =>
            andB (Nat.blt p 16) (Nat.beq (FE.T p) (pc (pc t (FE.T i)) ti))))))

@[expose] noncomputable def FX (j : Nat) : Nat :=
  nIf(Nat.beq j 0, nat_lit 3, nIf(Nat.beq j 1, nat_lit 8, nIf(Nat.beq j 2, nat_lit 10,
    nIf(Nat.beq j 3, nat_lit 13, nIf(Nat.beq j 4, nat_lit 19, nat_lit 40)))))

@[expose] noncomputable def rejF (t : Nat) : Bool :=
  notB (allN 6 fun j => notB (CFSG.KC.L34Pre.mvFix 6 16 FE.T t (FX j)))

@[expose] noncomputable def vs (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => allN 1344 fun i =>
    strictB (Nat.add (Nat.mul 1344 s) i) fun k => strictB (L34R.T k) fun t => orB (rejF t) (vK e k t)

@[expose] noncomputable def yK (y : Nat) : Bool :=
  strictB (YP y) fun p =>
    andB (canonK 16 5 (mask 5) (16 * 5) p)
      (andB (orB (Nat.beq p (pidn 16 5))
        (Nat.ble (CFSG.PSL3Four.Native.countBelow 16 fun i => Nat.beq (pg 5 (mask 5) p i) i) 4))
      (orB (notB (Nat.beq (pc16 p p) (pidn 16 5))) (YI.elem y)))

@[expose] noncomputable def triK (a b c : Nat) : Bool :=
  strictB (YP (YI.getD a 0)) fun A => strictB (YP (YI.getD b 0)) fun B =>
  strictB (YP (YI.getD c 0)) fun C => strictB (pidn 16 5) fun e =>
    orB (Nat.beq A e) (orB (Nat.beq B e) (orB (Nat.beq B A)
      (orB (notB (andB (andB (Nat.beq (pc16 A B) (pc16 B A)) (Nat.beq (pc16 A C) (pc16 C A)))
        (Nat.beq (pc16 B C) (pc16 C B))))
      (orB (Nat.beq C e) (orB (Nat.beq C A) (orB (Nat.beq C B) (Nat.beq C (pc16 A B))))))))

end CertificateChecks.KernelLC.L34V1

end
