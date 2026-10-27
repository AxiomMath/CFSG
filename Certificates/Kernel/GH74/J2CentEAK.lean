module

public import Certificates.Kernel.GH74.J2CentE
public import Certificates.Kernel.GH74.J2Ev

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2CentEA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn
open CertificateChecks.KernelGH74.J2CentE

@[expose] noncomputable def fB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def orB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) y true x

@[expose] noncomputable def andB (x y : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false y x

@[expose] noncomputable def notB (x : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false x

@[expose] noncomputable def allR (n : Nat) (g : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => Bool.rec (motive := fun _ => Bool) false acc (g k)) n

@[expose] noncomputable def anyR (n : Nat) (g : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k acc => Bool.rec (motive := fun _ => Bool) acc true (g k)) n

@[expose] noncomputable def sqAt (g : Nat) : Bool :=
  anyR 32 fun i => notB (fB (cmK (J2E.T i) g (J2EAI i) g) fun c => Nat.beq (pc c c) idK)

@[expose] noncomputable def commSqAt (g : Nat) : Bool :=
  orB (notB (involK g)) (orB (anyR 32 fun i => Nat.beq g (J2E.T i))
    (andB (invEqK 315 9 (mask 9) (315 * 9) g g) (sqAt g)))

@[expose] noncomputable def commSlice (b len : Nat) : Bool :=
  allR len fun i => fB (J2C2.T (Nat.add b i)) commSqAt

@[expose] noncomputable def bitB (M i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight M i) 1) 1

@[expose] noncomputable def invMask (T : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc
    (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 i) (involK (T i)))) n

@[expose] noncomputable def maskOK (T : Nat → Nat) (n M : Nat) : Bool :=
  allR n fun i => orB (notB (involK (T i))) (bitB M i)

@[expose] noncomputable def rankZ (x y z : Nat) : Bool :=
  orB (notB (andB (commK x z) (commK y z)))
    (orB (Nat.beq y x) (orB (Nat.beq z x) (orB (Nat.beq z y) (Nat.beq z (pc x y)))))

@[expose] noncomputable def rankOK (T : Nat → Nat) (n M : Nat) : Bool :=
  allR n fun a => orB (notB (bitB M a)) (fB (T a) fun x =>
    allR n fun b => orB (notB (bitB M b)) (fB (T b) fun y =>
      orB (notB (commK x y)) (allR n fun c => orB (notB (bitB M c)) (fB (T c) fun z =>
        rankZ x y z))))

@[expose] noncomputable def sqBAt (x : Nat) : Bool := orB (notB (isId 4 x)) (isId 2 x)

theorem comm_0 : commSlice 0 640 = true := by decide +kernel

theorem comm_1 : commSlice 640 640 = true := by decide +kernel

theorem comm_2 : commSlice 1280 640 = true := by decide +kernel

theorem rank_ok : fB (invMask J2E.T 32) (fun M => andB (maskOK J2E.T 32 M) (rankOK J2E.T 32 M)) =
    true := by
  decide +kernel

theorem sqB_ok : allR 240 (fun k => fB (J2CB.T k) sqBAt) = true := by decide +kernel

end CertificateChecks.KernelGH74.J2CentEA
