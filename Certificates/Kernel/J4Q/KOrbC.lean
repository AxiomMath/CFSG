module

public import Certificates.Kernel.J4Q.KOrbMats
public import Certificates.Kernel.J4Q.KOrbPk
public import Certificates.Kernel.J4Q.X0Orb

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] noncomputable def kRec (o m k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (CFSG.KD.KOP.RF (Nat.div k 64)) (Nat.add (Nat.mul 64 (Nat.mod k 64)) o)) m

@[expose] noncomputable def kPL (k : Nat) : Nat := kRec 0 1048575 k

@[expose] noncomputable def kPar (k : Nat) : Nat := Nat.div (kPL k) 12

@[expose] noncomputable def kLab (k : Nat) : Nat := Nat.mod (kPL k) 12

@[expose] noncomputable def kTT (k g : Nat) : Nat :=
  Nat.land (Nat.shiftRight (CFSG.KD.KOP.UF (Nat.div k 64))
    (Nat.mul 16 (Nat.add (Nat.mul 12 (Nat.mod k 64)) g))) 65535

@[expose] noncomputable def kSig (i : Nat) : Nat := kRec 20 65535 i

@[expose] noncomputable def kSigI (k : Nat) : Nat := kRec 36 65535 k

@[expose] noncomputable def kDerK (k : Nat) : Bool :=
  xBoolEq (Nat.beq (mulJ c rm (CFSG.KD.KO.MSF k) (getN one XG 0)) (mulJ c rm (getN one XG 0) (CFSG.KD.KO.MSF k)))
    (inLK k KCOMM)

@[expose] noncomputable def kAtK (k : Nat) : Bool :=
  andB (andB (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (kPar k) k) (andB (Nat.blt (kLab k) 12)
        (Nat.beq (CFSG.KD.KO.MSF k) (mulJ c rm (CFSG.KD.KO.MSF (kPar k)) (getN one KG (kLab k))))))
      (Nat.beq (CFSG.KD.KO.MSF k) one) (Nat.beq k 0))
      (andB (Bool.rec (motive := fun _ => Bool) (Nat.blt (kPL k) (kPL (Nat.succ k))) true
        (orB (Nat.beq k 0) (Nat.beq (Nat.succ k) 15360))) (kDerK k)))
    (andB (allR 12 fun g => andB (andB (Nat.blt (kTT k g) 15360)
          (orB (Nat.beq (kTT k g) 0) (Nat.ble (kPL (kTT k g)) (Nat.add (Nat.mul 12 k) g))))
        (Nat.beq (mulJ c rm (CFSG.KD.KO.MSF k) (getN one KG g)) (CFSG.KD.KO.MSF (kTT k g))))
      (andB (andB (Nat.blt (kSig k) 15360) (andB (Nat.blt (kSigI k) 15360) (Nat.beq (kSig (kSigI k)) k)))
        (Bool.rec (motive := fun _ => Bool) (Nat.blt (CFSG.KD.KO.MSF (kSig k)) (CFSG.KD.KO.MSF (kSig (Nat.succ k)))) true
          (Nat.beq (Nat.succ k) 15360))))

@[expose] noncomputable def kcK (c : Nat) : Bool := allR 64 fun j => kAtK (Nat.add (Nat.mul 64 c) j)

@[expose] noncomputable def kcH (h c : Nat) : Bool := kcK (Nat.add (Nat.mul 120 h) c)

@[expose] noncomputable def kcA (c : Nat) : Bool := kcH 0 c

@[expose] noncomputable def kcB (c : Nat) : Bool := kcH 1 c

end CertificateChecks.KernelJ4Q

end
