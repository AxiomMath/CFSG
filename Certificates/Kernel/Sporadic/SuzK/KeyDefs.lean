module

public import Certificates.Kernel.Sporadic.SuzK.Data
public import Certificates.Kernel.Sporadic.SuzK.KeyData
public import CFSG.Certificates.Kernel.Orders.Mat3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.F3.Native CFSG.KS CFSG.KS.Row CFSG.KS.PEnum CFSG.KC.Enum CFSG.KC.Ord

@[expose] noncomputable def LO : Nat := Nat.sub (Nat.shiftLeft 1 4096) 1

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft 1 64) 1

@[expose] noncomputable def CI : Nat := rep1 64 64

@[expose] noncomputable def ONE : Nat := rep1 65 64

@[expose] noncomputable def UP : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.sub 64 i) 1)) 1)
      (Nat.succ (Nat.mul (Nat.succ 64) i)))) 64

@[expose] noncomputable def MUL : Nat → Nat → Nat := mul3s 64 4096 LO CI RM

@[expose] noncomputable def VLD : Nat → Bool := valid3 4096 LO

@[expose] noncomputable def kx (k : Nat) : Nat := rg (nat_lit 8192) (mask (nat_lit 8192)) KD (nat_lit 0) k

@[expose] noncomputable def lt (i : Nat) : Nat := rg (nat_lit 4096) (mask (nat_lit 4096)) LN (nat_lit 0) i

@[expose] noncomputable def ln (i : Nat) : V := ⟨lt (Nat.mul (nat_lit 2) i), lt (Nat.succ (Nat.mul (nat_lit 2) i))⟩

@[expose] noncomputable def x3 (i : Nat) : Nat :=
  Nat.add (lt (Nat.mul (nat_lit 2) i)) (Nat.shiftLeft (lt (Nat.succ (Nat.mul (nat_lit 2) i))) (nat_lit 4096))

@[expose] noncomputable def edge (g k : Nat) : Bool :=
  strictB (Bool.rec (motive := fun _ => Nat) (r32 BE k) (r32 AL k) (Nat.beq g (nat_lit 0))) fun y =>
    strictB (x3 g) fun G => strictB (kx k) fun X =>
      bAnd(VLD X, Nat.beq (MUL G X) (MUL (kx y) G))

@[expose] noncomputable def edgeSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 715)) fun g => strictB (Nat.mul (Nat.mod s (nat_lit 715)) (nat_lit 32)) fun lo =>
    allN (nat_lit 32) fun t => strictB (Nat.add lo t) fun k =>
      bIf(Nat.blt k (nat_lit 22880), edge g k, true)

@[expose] noncomputable def sortAt (i : Nat) : Bool :=
  strictB (r32 SO i) fun x => strictB (r32 SOI i) fun u =>
    bAnd(Nat.blt x (nat_lit 22880), bAnd(Nat.blt u (nat_lit 22880), bAnd(Nat.beq (r32 SO u) i,
      bIf(Nat.blt (Nat.succ i) (nat_lit 22880), Nat.blt (kx x) (kx (r32 SO (Nat.succ i))), true))))

@[expose] noncomputable def sortSl (s : Nat) : Bool :=
  strictB (Nat.mul s (nat_lit 352)) fun lo => allN (nat_lit 352) fun t => sortAt (Nat.add lo t)

@[expose] noncomputable def rootK : Bool := Nat.beq (kx (nat_lit 0)) (x3 (nat_lit 8))

end CertificateChecks.KernelSpor.SuzK

end
