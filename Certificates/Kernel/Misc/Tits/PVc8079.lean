module

public import Certificates.Kernel.Misc.Tits.JVc8073
public import Certificates.Kernel.Misc.Tits.Pi7092
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.PV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelMisc.TitsJT (Z C CI G GI)
open CertificateChecks.KernelMisc.TitsJT.V (X pt onB Bc pw memN spanF LAM EIX cls)

@[expose] noncomputable def Pi : Nat := CertificateChecks.KernelMisc.TitsPi.P

@[expose] noncomputable def XP (i p : Nat) : Nat :=
  nIf(Nat.blt i 512, X i p, X (Nat.sub i 512) (pt Pi p))

@[expose] noncomputable def cmP (i g : Nat) : Bool :=
  onB fun p => Nat.beq (XP i (pt g p)) (pt g (XP i p))

@[expose] noncomputable def zcP (i g : Nat) : Bool :=
  onB fun p => Nat.beq (XP i (pt g p)) (pt Z (pt g (XP i p)))

@[expose] noncomputable def PbP (i : Nat) : Bool :=
  allN 4 fun k => bIf(cmP i (TitsJ.S k), true, zcP i (TitsJ.S k))

@[expose] noncomputable def allcP (i : Nat) : Bool := allN 4 fun k => cmP i (TitsJ.S k)

@[expose] noncomputable def sqP (i : Nat) : Bool := onB fun p => Nat.beq (XP i (XP i p)) p

@[expose] noncomputable def isOneP (i : Nat) : Bool := onB fun p => Nat.beq (XP i p) p

@[expose] noncomputable def isZP (i : Nat) : Bool := onB fun p => Nat.beq (XP i p) (pt Z p)

@[expose] noncomputable def lbP (j i m : Nat) : Nat := nIf(cmP i (Bc j m), 0, pw m)

@[expose] noncomputable def lmP (j i : Nat) : Nat :=
  Nat.add (lbP j i 0) (Nat.add (lbP j i 1) (Nat.add (lbP j i 2) (Nat.add (lbP j i 3) (lbP j i 4))))

@[expose] noncomputable def lamP (j i : Nat) : Nat := Nat.add (lmP j i) (nIf(Nat.blt i 512, 0, 32))

@[expose] noncomputable def coverP (i : Nat) : Bool :=
  allL (fun v => memN v (spanF [lamP 0 i, lamP 4 i, lamP 3 i, lamP 2 i, lamP 1 i] [0])) LAM

@[expose] noncomputable def clsP (i : Nat) : Nat :=
  nIf(Nat.blt i 512, cls i, nIf(memN (Nat.sub i 512) EIX, 3, 2))

@[expose] noncomputable def test2 (i cl : Nat) : Bool :=
  bAnd(bIf(Nat.blt i 512, memN (lmP 0 i) LAM, bIf(isOneP i, false, true)),
    bIf(PbP i,
      bAnd(Nat.blt i 512, bAnd(Nat.beq cl 0, bAnd(cmP i Pi, bAnd(sqP i, bAnd(Nat.beq (lmP 0 i) 0,
        bIf(allcP i, bIf(isOneP i, true, isZP i), true)))))),
      bAnd(bIf(Nat.beq cl 0, false, true),
        bIf(Nat.beq (lmP 0 i) 0,
          bAnd(Nat.beq cl 3, bIf(sqP i, false, true)),
          bAnd(bIf(Nat.beq cl 3, false, true),
            bAnd(bIf(Nat.beq (lamP 4 i) (lamP 0 i), false, true), bAnd(coverP i,
              Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (sqP i))
                (sqP i) (Nat.beq cl 1))))))))

theorem enumP : allN 1024 (fun i => test2 i (clsP i)) = true := by quickRfl

theorem z2 : V.isZ 2 = true := by quickRfl

end CertificateChecks.KernelMisc.TitsJT.PV

end
