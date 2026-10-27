module

public import Certificates.Kernel.LocalComp.L34Bo.Defs
public import Certificates.Data.Kernel.L34Norm
public import Certificates.Kernel.LocalComp.L34NData

public section

namespace CertificateChecks.KernelLC.L34Gr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.KC.L34Scan CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB anyN)

@[expose] noncomputable def X0 : Nat :=
  4566403543482620374936787432941360499159627687327558066587791034966992760896

@[expose] noncomputable def top : Bool :=
  andB (L34Bo.inS X0) (andB (Nat.beq (L34Bo.fa 0) 1) (andB (Nat.beq (L34Bo.fb 0) 27)
    (allN 42 fun p => orB (Nat.beq p 1) (orB (Nat.beq p 27)
      (notB (allN 4 fun i => Nat.beq (pg 6 (mask 6) (L34Bo.syG 0 i) p) p))))))

@[expose] noncomputable def inY (x0 v : Nat) : Bool :=
  andB (Nat.beq (Nat.mod (Nat.div v 4) 2) 1) (commPt 42 6 (L34R.T (Nat.div v 32)) x0)

@[expose] noncomputable def sq (r : Nat) : Nat := pcomp 42 6 (mask 6) r r

@[expose] noncomputable def yPt (e x0 r : Nat) : Bool :=
  andB (orB (notB (Nat.beq (sq (sq r)) e)) (Nat.beq (sq r) e))
    (orB (notB (Nat.beq (sq r) e)) (orB (Nat.beq r e)
      (andB (allN 7755 fun q => strictB (L34N.J q) fun v =>
          bIf(inY x0 v, strictB (L34R.T (Nat.div v 32)) fun r' =>
            orB (notB (Nat.beq (sq r') e)) (orB (Nat.beq r' e)
              (orB (notB (commPt 42 6 r r')) (Nat.beq r r'))), true))
        (allN 20160 fun k => strictB (L34S.T k) fun t =>
          orB (notB (andB (commPt 42 6 t x0) (commPt 42 6 t r)))
            (orB (Nat.beq t e) (orB (Nat.beq t x0) (Nat.beq t (sq x0))))))))

@[expose] noncomputable def grY (e x0 : Nat) : Bool :=
  allN 7755 fun q => strictB (L34N.J q) fun v =>
    bIf(inY x0 v, yPt e x0 (L34R.T (Nat.div v 32)), true)

@[expose] noncomputable def grS (e x0 x : Nat) : Bool :=
  orB (notB (pairPt 6 1 27 x)) (orB (notB (o3Pt 42 6 e x))
    (anyN 7755 fun q => strictB (L34N.J q) fun v =>
      andB (Nat.beq (Nat.mod (Nat.div v 4) 2) 1) (conjPt 42 6 (L34R.T (Nat.div v 32)) x0 x)))

@[expose] noncomputable def grSl (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => scanSl (grS e X0) L34S.T 1120 s

end CertificateChecks.KernelLC.L34Gr

end
