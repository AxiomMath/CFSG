module

public import Certificates.Kernel.Fi22Fuse.Data
public import Certificates.Kernel.Fi22Flag.ChkDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Fuse

open CFSG.KC.Enum CFSG.KS.Fi22Cent CFSG.KS.Fi22L CertificateChecks.KernelFi22S
  CertificateChecks.KernelFi22Flag

@[expose] noncomputable def c25240B : List Nat :=
  [130, 273, 86211, 86544, 87505, 92685, 100657, 102250, 112738, 113449]

@[expose] noncomputable def c25240C : List Nat :=
  [316, 40, 229, 638, 23, 257, 341, 456, 8, 360, 299, 10, 244, 531, 222, 28, 228, 146, 199, 64,
    277, 340, 66, 273, 283, 783]

@[expose] noncomputable def c25240bK (b x : Nat) : Nat :=
  strictN (List.getD c25240B b (nat_lit 0)) fun c =>
    gK (Nat.div c (nat_lit 128)) (Nat.mod c (nat_lit 128)) x

@[expose] noncomputable def c25240flagK : Bool := allN (nat_lit 10) fun b => c24671flagF (c25240bK b)

@[expose] noncomputable def c25240q (i : Nat) : Nat := List.getD QL i (nat_lit 0)

@[expose] noncomputable def c25240ev (m i : Nat) : Nat :=
  lk D.EV (Nat.add (Nat.mul (nat_lit 13) m) i)

@[expose] noncomputable def c25240ev0 : Bool :=
  allN (nat_lit 13) fun i => Nat.beq (c25240ev (nat_lit 0) i) (c25240q i)

@[expose] noncomputable def c25240evSl (b : Nat) : Bool :=
  allN (Nat.pow (nat_lit 2) b) fun d => allN (nat_lit 13) fun i =>
    Nat.beq (c25240ev (Nat.add (Nat.pow (nat_lit 2) b) d) i) (c25240bK b (c25240ev d i))

@[expose] noncomputable def c25240agE (H : Nat → Nat) (m : Nat) : Bool :=
  allN (nat_lit 13) fun i => Nat.beq (H (c25240q i)) (c25240ev m i)

@[expose] noncomputable def c25240inE (H : Nat → Nat) : Bool :=
  strictB (lk D.POS (H (nat_lit 0))) fun m =>
    bAnd(Nat.blt m (nat_lit 1024), c25240agE H m)

@[expose] noncomputable def c25240cj (u : Nat) (G : Nat → Nat) (x : Nat) : Nat :=
  strictN (cK u x) fun y => strictN (G y) (cK u)

@[expose] noncomputable def c25240anyC (G : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun u _ ih => bIf(c25240inE (c25240cj u G), true, ih)) c25240C

@[expose] noncomputable def c25240F (G : Nat → Nat) : Bool :=
  bIf(anyMv (sq G), true, bIf(allFix G, true, bIf(c25240inE G, true, c25240anyC G)))

@[expose] noncomputable def c25240Sl (c : Nat) : Bool :=
  allN (nat_lit 8) fun d => strictB (Nat.add (Nat.mul c (nat_lit 8)) d) fun k =>
    allN (nat_lit 128) fun j => c25240F (gK k j)

end CertificateChecks.KernelFi22Fuse

end
