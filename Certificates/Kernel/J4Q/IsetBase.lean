module

public import Certificates.Kernel.J4Q.IsetData
public import Certificates.Kernel.J4Q.IsetPk
public import CFSG.Sporadic.J4.QT2LocX0Data
public import CFSG.Sporadic.J4.QTRankInvData
public import Certificates.Data.Kernel.J4Q.Pack
public import Certificates.Data.Kernel.J4Q.QT2A
public import Certificates.Kernel.J4Q.Mat

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.IS CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] noncomputable def fldI (x w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def ich (F : Nat → Nat) (k : Nat) : Nat := fldI (F (Nat.div k 64)) 32 (Nat.mod k 64)

@[expose] noncomputable def iKey (k : Nat) : Nat := fldI (IKF (Nat.div k 64)) 128 (Nat.mod k 64)

@[expose] noncomputable def iTS (k : Nat) : List Nat := unpackP (iKey k)

@[expose] noncomputable def iPL (k : Nat) : Nat := ich IPF k

@[expose] noncomputable def iPar (k : Nat) : Nat := Nat.div (iPL k) 6

@[expose] noncomputable def iLab (k : Nat) : Nat := Nat.mod (iPL k) 6

@[expose] noncomputable def iTT (k g : Nat) : Nat :=
  fldI (ITF (Nat.div k 64)) 32 (Nat.add (Nat.mul 6 (Nat.mod k 64)) g)

@[expose] noncomputable def iSig (i : Nat) : Nat := ich ISF i

@[expose] noncomputable def iSigI (k : Nat) : Nat := ich IIF k

@[expose] noncomputable def lcB (g p : Nat) : Nat :=
  compB (getN 0 LPL g) (compB p (getN 0 LPL (Nat.mod (Nat.add g 3) 6)))

@[expose] noncomputable def idP : Nat := getN 0 IDP 0

@[expose] noncomputable def iAtK (k : Nat) : Bool :=
  (fun p => andB (andB (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (iPar k) k) (andB (Nat.blt (iLab k) 6) (Nat.beq p (lcB (iLab k) (iKey (iPar k))))))
      true (Nat.blt k 192))
      (andB (Bool.rec (motive := fun _ => Bool) (Nat.blt (iPL k) (iPL (Nat.succ k))) true
        (orB (Nat.blt k 192) (Nat.beq (Nat.succ k) 43264)))
        (andB (Nat.blt p (Nat.shiftLeft 1 121)) (Nat.beq (compB p p) idP))))
    (andB (allR 6 fun g => andB (andB (Nat.blt (iTT k g) 43264)
          (orB (Nat.blt (iTT k g) 192) (Nat.ble (iPL (iTT k g)) (Nat.add (Nat.mul 6 k) g))))
        (Nat.beq (lcB g p) (iKey (iTT k g))))
      (andB (andB (Nat.blt (iSig k) 43264) (andB (Nat.blt (iSigI k) 43264) (Nat.beq (iSig (iSigI k)) k)))
        (Bool.rec (motive := fun _ => Bool) (Nat.blt (iKey (iSig k)) (iKey (iSig (Nat.succ k)))) true
          (Nat.beq (Nat.succ k) 43264))))) (iKey k)

@[expose] noncomputable def icK (c : Nat) : Bool := allR 64 fun j => iAtK (Nat.add (Nat.mul 64 c) j)

@[expose] noncomputable def icH (h c : Nat) : Bool := icK (Nat.add (Nat.mul 338 h) c)

@[expose] noncomputable def icA (c : Nat) : Bool := icH 0 c

@[expose] noncomputable def icB (c : Nat) : Bool := icH 1 c

end CertificateChecks.KernelJ4Q

end
