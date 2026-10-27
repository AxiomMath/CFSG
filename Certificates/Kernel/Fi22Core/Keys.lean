module

public import Certificates.Kernel.Fi22Core.Data
public import Certificates.Data.Kernel.Fi22.Letters
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public meta import Certificates.Data.Kernel.Fi22.Orb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

open CFSG.F3.Native CFSG.Sporadic.Fi22.Native

meta def hexDig (c : Char) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else if c.toNat < 71 then c.toNat - 55 else c.toNat - 87

meta def fields12 (s : String) (n : Nat) : Array Nat :=
  let cs := (s.toList.filter fun c => c.isAlphanum).toArray
  let ds := (Array.replicate (3 * n - cs.size) '0' ++ cs).map hexDig
  Array.ofFn (n := n) fun e =>
    let b := 3 * n - 3 * (e.val + 1)
    ds[b]! * 256 + ds[b + 1]! * 16 + ds[b + 2]!

meta def orbE : Array Nat := fields12 orbText (4 * 3510)

meta def spreadM : Nat := (List.range 77).foldl (fun a b => a ||| (1 <<< (77 * b))) 0
meta def maskM : Nat := 2 ^ 77 - 1
meta def mulM (X Y : V) : V :=
  (List.range 77).foldl (fun acc j =>
    let yp := (Y.p >>> (77 * j)) &&& maskM
    let ym := (Y.m >>> (77 * j)) &&& maskM
    let sp := (X.p >>> j) &&& spreadM
    let sm := ((X.m ^^^ (X.m &&& X.p)) >>> j) &&& spreadM
    acc.add ⟨(sp * yp) ||| (sm * ym), (sp * ym) ||| (sm * yp)⟩) V.zero

meta def laneV (X : Array V) : V :=
  ⟨(List.range 77).foldl (fun a i => a + X[i]!.p * 2 ^ (77 * i)) 0,
    (List.range 77).foldl (fun a i => a + X[i]!.m * 2 ^ (77 * i)) 0⟩

meta def keysM : Array V := Id.run do
  let A := laneV (matA ())
  let B := laneV (matB ())
  let Bi := laneV (matBi ())
  let mut K : Array V := #[A]
  for k in [1:3510] do
    let X := K[orbE[2 * 3510 + k]!]!
    K := K.push (if orbE[3 * 3510 + k]! == 1 then mulM (mulM A X) A else mulM (mulM B X) Bi)
  return K

meta def kdM : Array Nat := keysM.map fun v => v.p + 2 ^ 5929 * v.m

meta def soM : Array Nat := (List.range 3510).toArray.qsort fun i j => kdM[i]! < kdM[j]!

meta def soiM : Array Nat := Id.run do
  let mut r := Array.replicate 3510 0
  for i in [0:3510] do
    r := r.set! soM[i]! i
  return r

end CertificateChecks.KernelFi22C

#krowsw CertificateChecks.KernelFi22C.KD 11858 CertificateChecks.KernelFi22C.kdM
#krows CertificateChecks.KernelFi22C.SO CertificateChecks.KernelFi22C.soM
#krows CertificateChecks.KernelFi22C.SOI CertificateChecks.KernelFi22C.soiM

namespace CertificateChecks.KernelFi22C

open CFSG.F3.Native CFSG.KS CFSG.KS.Row CFSG.KS.F3L CFSG.KS.Fi22L CFSG.KS.PEnum CFSG.KC.Enum

@[expose] noncomputable def kx (k : Nat) : Nat :=
  rg (nat_lit 11858) (mask (nat_lit 11858)) KD (nat_lit 0) k

@[expose] noncomputable def KL (k : Nat) : V :=
  strictT (kx k) fun x => ⟨Nat.land x (mk (nat_lit 5929)), Nat.shiftRight x (nat_lit 5929)⟩

@[expose] noncomputable def GL (g : Nat) : V :=
  Bool.rec (motive := fun _ => V) LB LA (Nat.beq g (nat_lit 0))

@[expose] noncomputable def edge (g k : Nat) : Bool :=
  strictB (lk (orbT g) k) fun y => eqF (mulF (GL g) (KL k)) (mulF (KL y) (GL g))

@[expose] noncomputable def edgeSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 110)) fun g => strictB (Nat.mul (Nat.mod s (nat_lit 110)) (nat_lit 32)) fun lo =>
    allN (nat_lit 32) fun t => strictB (Nat.add lo t) fun k =>
      bIf(Nat.blt k (nat_lit 3510), bAnd(canonF (KL k), edge g k), true)

@[expose] noncomputable def sortAt (i : Nat) : Bool :=
  strictB (r32 SO i) fun x => strictB (r32 SOI i) fun u =>
    bAnd(Nat.blt x (nat_lit 3510), bAnd(Nat.blt u (nat_lit 3510), bAnd(Nat.beq (r32 SO u) i,
      bIf(Nat.blt (Nat.succ i) (nat_lit 3510), Nat.blt (kx x) (kx (r32 SO (Nat.succ i))), true))))

@[expose] noncomputable def sortSl (s : Nat) : Bool :=
  strictB (Nat.mul s (nat_lit 351)) fun lo => allN (nat_lit 351) fun t => sortAt (Nat.add lo t)

@[expose] noncomputable def rootK : Bool := eqF (KL (nat_lit 0)) LA

end CertificateChecks.KernelFi22C

end
