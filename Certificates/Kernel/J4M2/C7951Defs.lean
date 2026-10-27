module

public import Certificates.Data.Kernel.J4Q.QT2A
public import Certificates.Kernel.J4Q.QTBase

public section

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CertificateChecks.KernelJ4Q

@[expose] noncomputable def pt77Masks : List Nat := [133, 778, 911, 1131, 1262, 1889, 2020]

@[expose] noncomputable def pt77One (t : Nat) (x : Nat × Nat × Nat × Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun ci y => Prod.rec (motive := fun _ => Bool)
    (fun j z => Prod.rec (motive := fun _ => Bool) (fun k w =>
      andB (Nat.blt ci (nat_lit 7)) (andB (Nat.blt j (nat_lit 11)) (andB (Nat.blt k (nat_lit 112))
        (andB (Nat.blt w (Nat.shiftLeft (nat_lit 1) (nat_lit 112)))
          (strictB (Nat.shiftLeft (nat_lit 1) k) fun v => strictB (getN one Us j) fun U =>
            strictB (etaK c rm one Us (getN 0 pt77Masks ci)) fun e =>
              andB (Nat.beq (vecJ rm w t) (vecJ rm (vecJ rm v t) U))
                (notB (Nat.beq (vecJ rm (vecJ rm (vecJ rm v e) t) U) (vecJ rm (vecJ rm w e) t)))))))) z) y) x

@[expose] noncomputable def pt77K (TL : List Nat) (W : List (Nat × Nat × Nat × Nat)) : Bool :=
  allR 76 fun i => pt77One (getN one TL (Nat.succ i)) (W.getD i (0, 0, 0, 0))

end CertificateChecks.KernelJ4M2

end
