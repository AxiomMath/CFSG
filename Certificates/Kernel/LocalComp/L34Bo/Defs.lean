module

public import Certificates.Kernel.LocalComp.L34Bo.Data
public import Certificates.Kernel.LocalComp.L34Un.Data
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Data.Kernel.L34Scan
public import Certificates.Data.Kernel.L34Pre
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CertificateChecks.KernelLC.L34Bo

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def syT (j q : Nat) : Nat :=
  nIf(Nat.beq j 0, SY0.T q, nIf(Nat.beq j 1, SY1.T q, nIf(Nat.beq j 2, SY2.T q,
    nIf(Nat.beq j 3, SY3.T q, nIf(Nat.beq j 4, SY4.T q, SY5.T q)))))

@[expose] noncomputable def syPL (j q : Nat) : Nat :=
  nIf(Nat.beq j 0, SY0.PL q, nIf(Nat.beq j 1, SY1.PL q, nIf(Nat.beq j 2, SY2.PL q,
    nIf(Nat.beq j 3, SY3.PL q, nIf(Nat.beq j 4, SY4.PL q, SY5.PL q)))))

@[expose] noncomputable def syG (j i : Nat) : Nat :=
  nIf(Nat.beq j 0, SY0.G i, nIf(Nat.beq j 1, SY1.G i, nIf(Nat.beq j 2, SY2.G i,
    nIf(Nat.beq j 3, SY3.G i, nIf(Nat.beq j 4, SY4.G i, SY5.G i)))))

@[expose] noncomputable def UI : Nat := pinvS 42 6 (mask 6) (UE0.G 0)

@[expose] noncomputable def cj (x : Nat) : Nat :=
  pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (UE0.G 0) x) UI

@[expose] noncomputable def inSY (j x : Nat) : Bool :=
  notB (allN 64 fun q => notB (Nat.beq (syT j q) x))

@[expose] noncomputable def fa (j : Nat) : Nat := L34BoG.FX.getD (Nat.mul 2 j) 0

@[expose] noncomputable def fb (j : Nat) : Nat := L34BoG.FX.getD (Nat.add (Nat.mul 2 j) 1) 0

@[expose] noncomputable def inSYf (j x : Nat) : Bool :=
  andB (Nat.beq (pg 6 (mask 6) x (fa j)) (fa j))
    (andB (Nat.beq (pg 6 (mask 6) x (fb j)) (fb j)) (inSY j x))

@[expose] noncomputable def inS (x : Nat) : Bool :=
  notB (allN 20160 fun q => notB (Nat.beq (L34S.T q) x))

@[expose] noncomputable def covK (e x : Nat) : Bool :=
  strictB (cj x) fun x1 => strictB (cj x1) fun x2 =>
    orB (Nat.beq x e) (orB (notB (invPt 42 6 x)) (orB (notB (commPt 42 6 x x1))
      (notB (allN 6 fun j => notB (allN 20160 fun q => strictB (L34S.T q) fun s =>
        orB (notB (andB (commPt 42 6 s x) (andB (commPt 42 6 s x1) (commPt 42 6 s x2))))
          (inSYf j s))))))

@[expose] noncomputable def normK (j e x : Nat) : Bool :=
  strictB (pinvS 42 6 (mask 6) x) fun si =>
    andB (canonK 42 6 (mask 6) (42 * 6) si) (andB (Nat.beq (pcomp 42 6 (mask 6) x si) e)
      (andB (Nat.beq (pcomp 42 6 (mask 6) si x) e)
        (orB (notB (allN 4 fun i => inSYf j (pcomp 42 6 (mask 6)
            (pcomp 42 6 (mask 6) x (syG j i)) si)))
          (orB (inSYf j x) (orB (inSYf j (pcomp 42 6 (mask 6) UI x))
            (inSYf j (pcomp 42 6 (mask 6) UI (pcomp 42 6 (mask 6) UI x))))))))

@[expose] noncomputable def cov (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => scanSl (covK e) L34S.T 1120 s

@[expose] noncomputable def rejB (j x : Nat) : Bool :=
  orB (CFSG.KC.L34Pre.mvFix 6 64 (syT j) x (fa j)) (CFSG.KC.L34Pre.mvFix 6 64 (syT j) x (fb j))

@[expose] noncomputable def nrm (j s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => scanSl (fun x => orB (rejB j x) (normK j e x)) L34S.T 1120 s

@[expose] noncomputable def sylK (j : Nat) (k cnt : Nat) (G GI T PL POS SRT SRI : Nat → Nat)
    (gs : Array (Array Nat)) : Bool :=
  andB (Nat.beq k 4) (andB (Nat.beq cnt 64) (andB (gensK gs 42 6 4 G)
    (andB (penumHdK (pidn 42 6) cnt 64 T PL)
    (andB (penumSlK 42 6 (mask 6) (42 * 6) false G GI k cnt T PL POS SRT SRI 0 64)
    (andB (allN 4 fun i => andB (inS (G i)) (Nat.beq (syG j i) (G i)))
      (allN 64 fun q => andB (Nat.beq (syT j q) (T q))
        (andB (Nat.beq (syPL j q) (PL q)) (inSY j (cj (T q))))))))))

end CertificateChecks.KernelLC.L34Bo

end
