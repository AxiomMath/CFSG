module

public import Certificates.Kernel.J4Q.VcK
public import Certificates.Kernel.J4Q.OrbBase
public import Certificates.Kernel.J4Q.B7Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q

@[expose] noncomputable def b7Xi : Nat := getN one XG 0

@[expose] noncomputable def b7XiI : Nat := getN one XG 8

@[expose] noncomputable def b7TW : List Int := List.append (getW vB7W 0) (getW vB7W 1)

@[expose] noncomputable def b7G0W : List Int := [-2, -3, -1, -2, -3, -3, -2, -1, -1, -5, -5, -5, -4, -5]

@[expose] noncomputable def b7LitOK : Bool :=
  andB (Nat.beq (getN one B7V 0) (wordJ c rm one G5 G5i b7TW))
    (andB (allR 3 fun i => Nat.beq (getN one B7V (Nat.succ i)) (mulJ c rm (mulJ c rm b7Xi (getN one B7V i)) b7XiI))
    (andB (canonJ pad B7G0I) (andB (Nat.beq (mulJ c rm (wordJ c rm one G5 G5i b7G0W) B7G0I) one)
    (andB (Nat.beq b7Xi (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] [1, 2, -3, 1, 2, -3]))
    (andB (canonJ pad b7XiI) (Nat.beq (mulJ c rm b7Xi b7XiI) one))))))

@[expose] noncomputable def b7Fixed (x : Nat) : Bool :=
  (fun q => allR 4 fun i => Nat.beq (vecJ rm q (getN one B7V i)) q) (vecJ rm x B7G0I)

@[expose] noncomputable def b7CH (ℓ : Nat) : List (List Nat) :=
  Bool.rec (motive := fun _ => List (List Nat)) CH6 CH5 (Nat.beq ℓ 5)

@[expose] noncomputable def b7FX (ℓ : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) FX6 FX5 (Nat.beq ℓ 5)

@[expose] noncomputable def b7FixK (ℓ i : Nat) : Bool :=
  allLK (fun e => (fun x => orB (notB (b7Fixed x)) (inLK x (b7FX ℓ))) (Nat.land e rm)) (getL (b7CH ℓ) i)

@[expose] noncomputable def b7Fix5 (i : Nat) : Bool := b7FixK 5 i

@[expose] noncomputable def b7Fix6 (i : Nat) : Bool := b7FixK 6 i

@[expose] noncomputable def b7Roots : Bool :=
  andB (orB (notB (b7Fixed (repK 5))) (inLK (repK 5) FX5))
    (orB (notB (b7Fixed (repK 6))) (inLK (repK 6) FX6))

@[expose] noncomputable def b7ActK (Mq : Nat) (t : List Nat) : Bool :=
  andB (Nat.beq (lenK t) 11) (allR 11 fun j => andB (Nat.blt (getN 0 t j) 2048)
    (Nat.beq (mulJ c rm (mulJ c rm Mq (getN one Us j)) Mq) (CFSG.KD.ETA.EF (getN 0 t j))))

@[expose] noncomputable def b7CandK (qv : Nat) (kw : List Int) (k : Nat) (t : List Nat) : Bool :=
  orB (Nat.beq (vecJ rm qv b7Xi) qv)
    ((fun K Ki M => andB (canonJ pad Ki) (andB (Nat.beq (mulJ c rm K Ki) one)
      (andB (Nat.beq (vecJ rm (v2N CFSG.Sporadic.J4.Native.rootV) Ki) qv)
      (andB (Nat.ble 1 k) (andB (Nat.blt k 16) (andB (notB (Nat.beq M one))
      (andB (Nat.beq (mulJ c rm M M) one)
      (andB (b7ActK (mulJ c rm (mulJ c rm Ki M) K) t) (notB (Nat.beq (fixFrom t 2048) 128))))))))))
      (wordJ c rm one G5 G5i kw) (wordJ c rm one G5 G5i (negRev kw)) (etaK c rm one B7V k))

@[expose] noncomputable def b7Pt (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (v2N CFSG.Sporadic.J4.Native.rootV)
    (fun j' _ => getN 0 (List.append FX5 FX6) j') j

@[expose] noncomputable def b7Word (j : Nat) : List Int := List.map (fun n => Int.subNatNat n 5) (getL WW j)

@[expose] noncomputable def b7WitK (j : Nat) : Bool :=
  b7CandK (vecJ rm (b7Pt j) B7G0I) (b7Word j) (getN 0 WK j) (getL WT j)

@[expose] noncomputable def b7VK : Bool :=
  andB (Nat.beq (mulJ c rm b7Xi b7XiI) one)
    (andB (allR 4 fun i => Nat.beq (mulJ c rm (getN one B7V i) (getN one B7V i)) one)
    (andB (allR 4 fun i => allR 4 fun j => Nat.beq (mulJ c rm (getN one B7V i) (getN one B7V j))
      (mulJ c rm (getN one B7V j) (getN one B7V i)))
    (andB (Nat.beq (mulJ c rm (mulJ c rm b7Xi (getN one B7V 3)) b7XiI) (etaK c rm one B7V 15))
    (andB (Nat.beq (vecJ rm (v2N CFSG.Sporadic.J4.Native.rootV) (getN one B7V 0))
      (v2N CFSG.Sporadic.J4.Native.rootV))
    (andB (Nat.beq (mulJ c rm (wordJ c rm one G5 G5i b7G0W) B7G0I) one)
    (andB (inLK 387 (fstsK (ptsK OR.s0)))
      (Nat.beq (mulJ c rm (mulJ c rm B7G0I (getN one B7V 0)) (wordJ c rm one G5 G5i b7G0W))
        (CFSG.KD.ETA.EF 387))))))))

@[expose] noncomputable def b7EK : List Nat := smapK (fun i => wordJ c rm one G5 G5i (getW vB7W i)) (rangeK 4)

@[expose] noncomputable def b7CrossK (A B : List Nat) : Bool :=
  allR 4 fun j => notB (allR 16 fun k => notB (Nat.beq (getN one A j) (etaK c rm one B k)))

@[expose] noncomputable def b7CrossOK : Bool :=
  (fun E => andB (b7CrossK B7V E) (b7CrossK E B7V)) b7EK

@[expose] noncomputable def b7BaseK (k : Nat) : Bool :=
  (fun M => orB (Nat.beq M one) (andB (Nat.beq (mulJ c rm one one) one)
    (andB (Nat.beq (mulJ c rm M M) one)
    (andB (b7ActK (mulJ c rm (mulJ c rm one M) one) (getL BT (Nat.sub k 1)))
      (Nat.beq (fixFrom (getL BT (Nat.sub k 1)) 2048) 128)))))
    (etaK c rm one B7V k)

end CertificateChecks.KernelJ4Q

end
