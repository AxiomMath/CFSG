module

public import Certificates.Kernel.TwoHSLe4.NormD
public import Certificates.Data.Kernel.F4M3B
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Cand

public section

namespace CertificateChecks.KernelTwoHSLe4.NormP

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.F4M3B

meta def cpM : Array (Array ℕ) := candData.toArray.map List.toArray

end CertificateChecks.KernelTwoHSLe4.NormP

#kmisc_packarrs CertificateChecks.KernelTwoHSLe4.NormP.CP CertificateChecks.KernelTwoHSLe4.NormP.cpM 2

namespace CertificateChecks.KernelTwoHSLe4.NormP

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.F4M3B CertificateChecks.KernelTwoHSLe4.Norm

@[expose] def fd (P k : ℕ) : ℕ := Nat.land (Nat.shiftRight P (Nat.mul 2 k)) 3

@[expose] def dR (P : ℕ) : R4 :=
  ⟨fd P 0, fd P 1, fd P 2, fd P 3, fd P 4, fd P 5, fd P 6, fd P 7, fd P 8, fd P 9, fd P 10,
    fd P 11, fd P 12, fd P 13, fd P 14, fd P 15⟩

@[expose] noncomputable def candK : List R4 := (List.range 256).map fun j => dR (CP j)

variable {α : Type}

structure Q4 (α : Type) where
  e00 : α × α
  e01 : α × α
  e02 : α × α
  e03 : α × α
  e10 : α × α
  e11 : α × α
  e12 : α × α
  e13 : α × α
  e20 : α × α
  e21 : α × α
  e22 : α × α
  e23 : α × α
  e30 : α × α
  e31 : α × α
  e32 : α × α
  e33 : α × α

structure V4 (α : Type) where
  v0 : α × α
  v1 : α × α
  v2 : α × α
  v3 : α × α

@[expose] def zr (o : Ops α) : α := o.x o.t o.t

@[expose] def mulE (o : Ops α) (p q : α × α) : α × α :=
  (o.a p.1 q.1, o.x (o.a p.1 q.2) (o.a p.2 q.1))

@[expose] def addE (o : Ops α) (p q : α × α) : α × α :=
  (o.x p.1 q.1, o.x (o.x p.2 q.2) (o.a p.1 q.1))

@[expose] def dotE (o : Ops α) (a0 b0 a1 b1 a2 b2 a3 b3 : α × α) : α × α :=
  addE o (addE o (addE o (mulE o a0 b0) (mulE o a1 b1)) (mulE o a2 b2)) (mulE o a3 b3)

@[expose] def eqE (o : Ops α) (p q : α × α) : α :=
  o.a (bnot o (o.x p.1 q.1)) (bnot o (o.x p.2 q.2))

@[expose] def mulM (o : Ops α) (A B : Q4 α) : Q4 α :=
  ⟨dotE o A.e00 B.e00 A.e01 B.e10 A.e02 B.e20 A.e03 B.e30,
   dotE o A.e00 B.e01 A.e01 B.e11 A.e02 B.e21 A.e03 B.e31,
   dotE o A.e00 B.e02 A.e01 B.e12 A.e02 B.e22 A.e03 B.e32,
   dotE o A.e00 B.e03 A.e01 B.e13 A.e02 B.e23 A.e03 B.e33,
   dotE o A.e10 B.e00 A.e11 B.e10 A.e12 B.e20 A.e13 B.e30,
   dotE o A.e10 B.e01 A.e11 B.e11 A.e12 B.e21 A.e13 B.e31,
   dotE o A.e10 B.e02 A.e11 B.e12 A.e12 B.e22 A.e13 B.e32,
   dotE o A.e10 B.e03 A.e11 B.e13 A.e12 B.e23 A.e13 B.e33,
   dotE o A.e20 B.e00 A.e21 B.e10 A.e22 B.e20 A.e23 B.e30,
   dotE o A.e20 B.e01 A.e21 B.e11 A.e22 B.e21 A.e23 B.e31,
   dotE o A.e20 B.e02 A.e21 B.e12 A.e22 B.e22 A.e23 B.e32,
   dotE o A.e20 B.e03 A.e21 B.e13 A.e22 B.e23 A.e23 B.e33,
   dotE o A.e30 B.e00 A.e31 B.e10 A.e32 B.e20 A.e33 B.e30,
   dotE o A.e30 B.e01 A.e31 B.e11 A.e32 B.e21 A.e33 B.e31,
   dotE o A.e30 B.e02 A.e31 B.e12 A.e32 B.e22 A.e33 B.e32,
   dotE o A.e30 B.e03 A.e31 B.e13 A.e32 B.e23 A.e33 B.e33⟩

@[expose] def mvM (o : Ops α) (A : Q4 α) (v : V4 α) : V4 α :=
  ⟨dotE o A.e00 v.v0 A.e01 v.v1 A.e02 v.v2 A.e03 v.v3,
   dotE o A.e10 v.v0 A.e11 v.v1 A.e12 v.v2 A.e13 v.v3,
   dotE o A.e20 v.v0 A.e21 v.v1 A.e22 v.v2 A.e23 v.v3,
   dotE o A.e30 v.v0 A.e31 v.v1 A.e32 v.v2 A.e33 v.v3⟩

@[expose] def eqM (o : Ops α) (A B : Q4 α) : α :=
  o.a (eqE o A.e00 B.e00) (o.a (eqE o A.e01 B.e01) (o.a (eqE o A.e02 B.e02)
  (o.a (eqE o A.e03 B.e03) (o.a (eqE o A.e10 B.e10) (o.a (eqE o A.e11 B.e11)
  (o.a (eqE o A.e12 B.e12) (o.a (eqE o A.e13 B.e13) (o.a (eqE o A.e20 B.e20)
  (o.a (eqE o A.e21 B.e21) (o.a (eqE o A.e22 B.e22) (o.a (eqE o A.e23 B.e23)
  (o.a (eqE o A.e30 B.e30) (o.a (eqE o A.e31 B.e31) (o.a (eqE o A.e32 B.e32)
  (eqE o A.e33 B.e33)))))))))))))))

@[expose] def eqV (o : Ops α) (v w : V4 α) : α :=
  o.a (eqE o v.v0 w.v0) (o.a (eqE o v.v1 w.v1) (o.a (eqE o v.v2 w.v2) (eqE o v.v3 w.v3)))

@[expose] def cB (o : Ops α) (n : ℕ) : α := Bool.rec (zr o) o.t (Nat.beq (Nat.mod n 2) 1)

@[expose] def cE (o : Ops α) (n : ℕ) : α × α := (cB o n, cB o (Nat.div n 2))

@[expose] def cQ (o : Ops α) (c : R4) : Q4 α :=
  ⟨cE o c.a00, cE o c.a01, cE o c.a02, cE o c.a03, cE o c.a10, cE o c.a11, cE o c.a12,
    cE o c.a13, cE o c.a20, cE o c.a21, cE o c.a22, cE o c.a23, cE o c.a30, cE o c.a31,
    cE o c.a32, cE o c.a33⟩

@[expose] def cV (o : Ops α) (v : RV) : V4 α := ⟨cE o v.v0, cE o v.v1, cE o v.v2, cE o v.v3⟩

@[expose] def inQ (o : Ops α) (b : R4) (h : ℕ → α) : Q4 α :=
  ⟨(cB o b.a00, h 0), (cB o b.a01, h 1), (cB o b.a02, h 2), (cB o b.a03, h 3),
   (cB o b.a10, h 4), (cB o b.a11, h 5), (cB o b.a12, h 6), (cB o b.a13, h 7),
   (cB o b.a20, h 8), (cB o b.a21, h 9), (cB o b.a22, h 10), (cB o b.a23, h 11),
   (cB o b.a30, h 12), (cB o b.a31, h 13), (cB o b.a32, h 14), (cB o b.a33, h 15)⟩

@[expose] def bindQ (o : Ops α) (A : Q4 α) (k : Q4 α → α) : α :=
  o.bd A.e00.1 fun l00 => o.bd A.e00.2 fun h00 => o.bd A.e01.1 fun l01 => o.bd A.e01.2 fun h01 =>
  o.bd A.e02.1 fun l02 => o.bd A.e02.2 fun h02 => o.bd A.e03.1 fun l03 => o.bd A.e03.2 fun h03 =>
  o.bd A.e10.1 fun l10 => o.bd A.e10.2 fun h10 => o.bd A.e11.1 fun l11 => o.bd A.e11.2 fun h11 =>
  o.bd A.e12.1 fun l12 => o.bd A.e12.2 fun h12 => o.bd A.e13.1 fun l13 => o.bd A.e13.2 fun h13 =>
  o.bd A.e20.1 fun l20 => o.bd A.e20.2 fun h20 => o.bd A.e21.1 fun l21 => o.bd A.e21.2 fun h21 =>
  o.bd A.e22.1 fun l22 => o.bd A.e22.2 fun h22 => o.bd A.e23.1 fun l23 => o.bd A.e23.2 fun h23 =>
  o.bd A.e30.1 fun l30 => o.bd A.e30.2 fun h30 => o.bd A.e31.1 fun l31 => o.bd A.e31.2 fun h31 =>
  o.bd A.e32.1 fun l32 => o.bd A.e32.2 fun h32 => o.bd A.e33.1 fun l33 => o.bd A.e33.2 fun h33 =>
  k ⟨(l00, h00), (l01, h01), (l02, h02), (l03, h03), (l10, h10), (l11, h11), (l12, h12),
    (l13, h13), (l20, h20), (l21, h21), (l22, h22), (l23, h23), (l30, h30), (l31, h31),
    (l32, h32), (l33, h33)⟩

@[expose] def bindL (o : Ops α) (L : List (Q4 α)) : (List (Q4 α) → α) → α :=
  List.rec (motive := fun _ => (List (Q4 α) → α) → α) (fun k => k [])
    (fun A _ ih k => bindQ o A fun A' => ih fun L' => k (A' :: L')) L

@[expose] def allA (o : Ops α) (L : List α) : α := L.foldr o.a o.t

@[expose] def anyA (o : Ops α) (L : List α) : α := L.foldr (bor o) (zr o)

@[expose] def finK (o : Ops α) (b : R4) (C : List R4) (A : Q4 α) (P Q : List (Q4 α)) : α :=
  bor o (bor o (eqV o (mvM o A (cV o tRV)) (cV o tRV))
      (bnot o (o.a (allA o (P.map fun p => anyA o (Q.map fun q => eqM o p q)))
        (allA o (Q.map fun q => anyA o (P.map fun p => eqM o p q))))))
    (o.a (eqV o (mvM o A (cV o tRV)) (cV o zpRV))
      (anyA o (C.map fun c => Bool.rec (zr o) (eqM o A (cQ o c)) (c.mod2 == b))))

@[expose] def chkK (o : Ops α) (b : R4) (L C : List R4) (h : ℕ → α) : α :=
  bindQ o (inQ o b h) fun A =>
    bindL o (L.map fun s => mulM o A (cQ o s)) fun P =>
      bindL o (L.map fun s => mulM o (cQ o s) A) fun Q => finK o b C A P Q

@[expose] def frcR (b : R4) (k : R4 → Bool) : Bool :=
  frc b.a00 fun a00 => frc b.a01 fun a01 => frc b.a02 fun a02 => frc b.a03 fun a03 =>
  frc b.a10 fun a10 => frc b.a11 fun a11 => frc b.a12 fun a12 => frc b.a13 fun a13 =>
  frc b.a20 fun a20 => frc b.a21 fun a21 => frc b.a22 fun a22 => frc b.a23 fun a23 =>
  frc b.a30 fun a30 => frc b.a31 fun a31 => frc b.a32 fun a32 => frc b.a33 fun a33 =>
  k ⟨a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33⟩

@[expose] def frcL (L : List R4) : (List R4 → Bool) → Bool :=
  List.rec (motive := fun _ => (List R4 → Bool) → Bool) (fun k => k [])
    (fun b _ ih k => frcR b fun b' => ih fun L' => k (b' :: L')) L

@[expose] def wf2B (b : R4) : Bool :=
  Nat.blt b.a00 2 && Nat.blt b.a01 2 && Nat.blt b.a02 2 && Nat.blt b.a03 2 &&
  Nat.blt b.a10 2 && Nat.blt b.a11 2 && Nat.blt b.a12 2 && Nat.blt b.a13 2 &&
  Nat.blt b.a20 2 && Nat.blt b.a21 2 && Nat.blt b.a22 2 && Nat.blt b.a23 2 &&
  Nat.blt b.a30 2 && Nat.blt b.a31 2 && Nat.blt b.a32 2 && Nat.blt b.a33 2

@[expose] noncomputable def chkNG (b : R4) (L C : List R4) : Bool :=
  wf2B b && frcR b fun b' => frcL L fun L' => frcL C fun C' =>
    frc (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1) fun t =>
      Nat.beq (chkK (natOps t) b' L' C' fun j => pln j 16) t

@[expose] noncomputable def chkN (b : R4) : Bool := chkNG b SL candK

end CertificateChecks.KernelTwoHSLe4.NormP

end
