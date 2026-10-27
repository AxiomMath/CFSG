module

public import Certificates.Data.Kernel.Fi22Twist.Lv
public import Certificates.Data.Kernel.Fi22Twist.Tf
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Fi22Twist.LData
public import Certificates.Kernel.Sporadic.Fi22.N3153Data
public import Certificates.Kernel.Sporadic.Fi22.X2069PT

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def TC (f : Nat) : Nat := nIf(Nat.blt f (nat_lit 865), TF f, TF2 (Nat.sub f (nat_lit 865)))

@[expose] noncomputable def TTC (f : Nat) : Nat :=
  nIf(Nat.blt f (nat_lit 865), TT f, TT2 (Nat.sub f (nat_lit 865)))

@[expose] noncomputable def ch431009lv_ (u : Nat) : Bool :=
  lvK OF PF CertificateChecks.KernelSpor.Fi22ChT.F u

@[expose] noncomputable def ch431009tp_ (k : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) k) (fun f => bIf(Nat.blt f (nat_lit 891), tfPtK TC TTC OF f, true))
    (nat_lit 64)

@[expose] noncomputable def ch431009tf2_ : Bool :=
  allBlk (nat_lit 865) (fun f => tfK TC TTC CertificateChecks.KernelSpor.Fi22ChT.F f) (nat_lit 26)

@[expose] noncomputable def ch431009nd_ (n : Nat) : Bool :=
  nodeK TC TTC OF CFSG.KD.N3153.M DF GF LF KF n

@[expose] noncomputable def ch431009rt_ : Bool := allBlk (nat_lit 0) (fun n => rootK LF n) (nat_lit 5)

end CertificateChecks.KernelFi22Twist

end
