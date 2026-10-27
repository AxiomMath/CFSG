module

public import Certificates.Data.Kernel.Fi22.Letters
public import CFSG.Certificates.Kernel.Orders.Fi22.Rels
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

open CFSG.KS.Fi22L CFSG.KC.Enum

@[expose] noncomputable def appL (l : Nat × Bool) (y : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (nIf(Nat.beq l.1 (nat_lit 0), lk (orbT (nat_lit 0)) y, reg ljPacked (nat_lit 2) y))
    (nIf(Nat.beq l.1 (nat_lit 0), lk (orbT (nat_lit 0)) y, lk (orbT (nat_lit 1)) y)) l.2

@[expose] noncomputable def wordAt (w : List (Nat × Bool)) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun l _ ih => strictN ih fun y => appL l y) w

@[expose] noncomputable def relAt (r x : Nat) : Bool :=
  Nat.beq (wordAt (List.getD CFSG.KD.OrdFi22.rels r []) x) x

@[expose] noncomputable def relSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 6)) fun r => strictB (Nat.mul (Nat.mod s (nat_lit 6)) (nat_lit 585)) fun lo =>
    allN (nat_lit 585) fun t => relAt r (Nat.add lo t)

end CertificateChecks.KernelFi22C

#kon_slices CertificateChecks.KernelFi22C.relSl 0 78

end
