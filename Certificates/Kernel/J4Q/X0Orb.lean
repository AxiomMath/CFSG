module

public import Certificates.Kernel.J4Q.X0Base
public import Certificates.Kernel.J4Q.X0OrbMats
public import Certificates.Kernel.J4Q.X0OrbPk
public import CFSG.Certificates.Kernel.J4Q.RepMOrb
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] noncomputable def ch64 (L : List (List Nat)) (k : Nat) : Nat :=
  getN 0 (L.getD (Nat.div k 64) []) (Nat.mod k 64)

@[expose] noncomputable def xRec (o m k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (CFSG.KD.X0P.RF (Nat.div k 64)) (Nat.add (Nat.mul 64 (Nat.mod k 64)) o)) m

@[expose] noncomputable def xPL (k : Nat) : Nat := xRec 0 1048575 k

@[expose] noncomputable def xPar (k : Nat) : Nat := Nat.div (xPL k) 16

@[expose] noncomputable def xLab (k : Nat) : Nat := Nat.mod (xPL k) 16

@[expose] noncomputable def xTT (k g : Nat) : Nat :=
  Nat.land (Nat.shiftRight (CFSG.KD.X0P.UF (Nat.div k 64))
    (Nat.mul 16 (Nat.add (Nat.mul 16 (Nat.mod k 64)) g))) 65535

@[expose] noncomputable def xSig (i : Nat) : Nat := xRec 20 65535 i

@[expose] noncomputable def xSigI (k : Nat) : Nat := xRec 36 65535 k

@[expose] noncomputable def inLK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq x y) ih) l

@[expose] noncomputable def xBoolEq (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def xDerK (k : Nat) : Bool :=
  andB (andB (Nat.blt (ch64 XQL k) 14) (Nat.beq (vecJ rm (v2N rootV) (CFSG.KD.X0O.MSF k)) (getN 0 XPTS (ch64 XQL k))))
    (xBoolEq (andB (notB (Nat.beq (CFSG.KD.X0O.MSF k) one)) (Nat.beq (mulJ c rm (CFSG.KD.X0O.MSF k) (CFSG.KD.X0O.MSF k)) one))
      (inLK k XINV))

@[expose] noncomputable def xAtK (k : Nat) : Bool :=
  andB (andB (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (xPar k) k) (andB (Nat.blt (xLab k) 16)
        (Nat.beq (CFSG.KD.X0O.MSF k) (mulJ c rm (CFSG.KD.X0O.MSF (xPar k)) (getN one XG (xLab k))))))
      (Nat.beq (CFSG.KD.X0O.MSF k) one) (Nat.beq k 0))
      (andB (Bool.rec (motive := fun _ => Bool) (Nat.blt (xPL k) (xPL (Nat.succ k))) true
        (orB (Nat.beq k 0) (Nat.beq (Nat.succ k) 6720))) (xDerK k)))
    (andB (allR 16 fun g => andB (andB (Nat.blt (xTT k g) 6720)
          (orB (Nat.beq (xTT k g) 0) (Nat.ble (xPL (xTT k g)) (Nat.add (Nat.mul 16 k) g))))
        (Nat.beq (mulJ c rm (CFSG.KD.X0O.MSF k) (getN one XG g)) (CFSG.KD.X0O.MSF (xTT k g))))
      (andB (andB (Nat.blt (xSig k) 6720) (andB (Nat.blt (xSigI k) 6720) (Nat.beq (xSig (xSigI k)) k)))
        (Bool.rec (motive := fun _ => Bool) (Nat.blt (CFSG.KD.X0O.MSF (xSig k)) (CFSG.KD.X0O.MSF (xSig (Nat.succ k)))) true
          (Nat.beq (Nat.succ k) 6720))))

@[expose] noncomputable def xcK (c : Nat) : Bool := allR 64 fun j => xAtK (Nat.add (Nat.mul 64 c) j)

#j4q_all CFSG.KD.J4Q.XC CertificateChecks.KernelJ4Q.xcK 105

theorem xAt_spec {k : Nat} (hk : k < 6720) : xAtK k = true := by
  have hc : Nat.div k 64 < 105 := by change k / 64 < 105; omega
  have h := allR_spec (XC.all (Nat.div k 64) hc) (Nat.mod k 64) (by change k % 64 < 64; omega)
  have e : Nat.add (Nat.mul 64 (Nat.div k 64)) (Nat.mod k 64) = k := by
    change 64 * (k / 64) + k % 64 = k
    omega
  rw [e] at h
  exact h

end CertificateChecks.KernelJ4Q

end
