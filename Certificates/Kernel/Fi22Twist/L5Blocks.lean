module

public import Certificates.Data.Kernel.Fi22Twist.Leaf
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Fi22Twist.LData
public import Certificates.Kernel.Fi22Twist.L5Data
public import Certificates.Kernel.Sporadic.Fi22.N3153Data
public import Certificates.Kernel.Sporadic.Fi22.X2069PT

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def t12 (L j : Nat) : Nat := fld(L, Nat.mul (nat_lit 12) j, nat_lit 4095)

@[expose] noncomputable def offC : Nat := nat_lit 4109878733741696360448

@[expose] noncomputable def szC : Nat := nat_lit 136897039836168354

@[expose] noncomputable def gofC : Nat := nat_lit 5067443101777920

@[expose] noncomputable def ngC : Nat := nat_lit 1407718531293188

@[expose] noncomputable def offU : Nat := nat_lit 1774711026129133965312

@[expose] noncomputable def szU : Nat := nat_lit 68448519917088849

@[expose] noncomputable def gofU : Nat := nat_lit 5630461757898752

@[expose] noncomputable def ngU : Nat := nat_lit 1407787284320260

@[expose] noncomputable def ch431009wf_ (k : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) k) (fun u =>
    bIf(Nat.blt u (nat_lit 728), wfK WF OF BF CertificateChecks.KernelSpor.Fi22ChT.F u, true)) (nat_lit 64)

@[expose] noncomputable def jOf (n : Nat) : Nat :=
  nIf(Nat.blt n (nat_lit 81), nat_lit 0, nIf(Nat.blt n (nat_lit 405), nat_lit 1,
    nIf(Nat.blt n (nat_lit 891), nat_lit 2, nIf(Nat.blt n (nat_lit 2835), nat_lit 3, nat_lit 4))))

@[expose] noncomputable def ch431009lf_ (k : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 16) k) (fun n =>
    bIf(Nat.blt n (nat_lit 2997),
      strictB (jOf n) fun j =>
      leafK TF DF CFSG.KD.N3153.M BF WF XF EF KF CK j n (t12 offC j) (t12 szC j), true)) (nat_lit 16)

@[expose] noncomputable def ch431009ob_ (u : Nat) : Bool :=
  strictB (Nat.div u (nat_lit 32)) fun j =>
  strictB (Nat.mod u (nat_lit 32)) fun k =>
  allBlk (Nat.mul (nat_lit 64) k) (fun i =>
    bAnd(bIf(Nat.blt i (t12 szC j),
        orbK CK CG (t12 gofC j) (t12 ngC j) (t12 offC j) (t12 szC j) i, true),
      bIf(Nat.blt i (t12 szU j),
        bAnd(orbK UK UG (t12 gofU j) (t12 ngU j) (t12 offU j) (t12 szU j) i,
          subK UK CK (t12 offU j) (t12 offC j) (t12 szC j) i), true))) (nat_lit 64)

@[expose] noncomputable def ch431009jx_ (j : Nat) : Bool :=
  (fun Dj : Nat → Nat =>
    bAnd(allBlk (nat_lit 0) (fun m => bAnd(commK CG DF (t12 gofC j) j m,
        normK NF CG UG UK j m (t12 gofC j) (t12 gofU j) (t12 ngU j) (t12 offU j) (t12 szU j)))
        (t12 ngC j),
      strictB (GF j) fun g =>
      strictB (HF j) fun h =>
      bAnd(allBlk (nat_lit 0) (fun d => relV Dj (fld(g, Nat.mul (nat_lit 1024) d,
          Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1024)) (nat_lit 1))) d) (nat_lit 3),
        bAnd(relV Dj (fld(h, nat_lit 0, Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1)))
            (nat_lit 3),
          bAnd(relV Dj (Nat.shiftRight h (nat_lit 256)) (nat_lit 4), relV Dj (XF j) (nat_lit 5))))))
  (fun e => DF (Nat.add (Nat.mul (nat_lit 27) j) e))

end CertificateChecks.KernelFi22Twist

end
