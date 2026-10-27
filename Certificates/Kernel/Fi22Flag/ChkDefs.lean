module

public import Certificates.Kernel.Fi22Syl.ChainDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Flag

open CFSG.KC.Enum CFSG.KS.Fi22Cent CertificateChecks.KernelFi22S

@[expose] def c24671F : List Nat :=
  [130, 273, 86211, 86544, 87505, 92685, 100657, 102250, 109538, 110138, 112738, 112807, 113449,
    113698, 117469, 117586, 120403, 121039, 122609, 124839, 125159, 126562]

@[expose] noncomputable def c24671mem (c : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun f _ ih => bIf(Nat.beq f c, true, ih)) c24671F

@[expose] noncomputable def c24671flagF (G : Nat → Nat) : Bool :=
  bAnd(allFix (sq G), bAnd(anyMv G, allFix (cb fun x => strictN (gA x) G)))

@[expose] noncomputable def c24671flag (k j : Nat) : Bool := c24671flagF (gK k j)

@[expose] noncomputable def c24671Sl (c : Nat) : Bool :=
  allN (nat_lit 8) fun d => strictB (Nat.add (Nat.mul c (nat_lit 8)) d) fun k =>
    allN (nat_lit 128) fun j =>
      bIf(c24671mem (Nat.add (Nat.mul k (nat_lit 128)) j), true, Bool.not (c24671flag k j))

end CertificateChecks.KernelFi22Flag

end
