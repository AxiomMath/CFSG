module

public import Certificates.Data.Kernel.J2Sig12648
public import Certificates.Kernel.J2Sig12648.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ2Sig

open CFSG.KC.Enum CFSG.KC.J2Sig CFSG.KS
open CertificateChecks.KernelMisc.J2C3 (X Z I AB)
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 (pairA wordA wordB)

@[expose] noncomputable def actP (j : Nat) : Nat := nIf(Nat.blt j (nat_lit 3), Z, X)

@[expose] noncomputable def conjE (A t e : Nat) : Nat :=
  nIf(Nat.beq e (nat_lit 0), t, nIf(Nat.beq e (nat_lit 1), m9 A (m9 t (m9 A A)),
    m9 (m9 A A) (m9 t A)))

@[expose] noncomputable def orbB : Bool :=
  CFSG.KC.LQT.P.allN 6 fun j => CFSG.KC.LQT.P.allN 3 fun p => CFSG.KC.LQT.P.allN 3 fun q =>
    CFSG.KC.LQT.P.anyN 3 fun e =>
      Nat.beq (conjE (actP j) (VV (Nat.add (Nat.mul 3 j) p)) e) (VV (Nat.add (Nat.mul 3 j) q))

@[expose] noncomputable def evW (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) I (fun l _ ih => m9 (VV l) ih) w

@[expose] noncomputable def pairB (pq : Nat × Nat) : Bool :=
  strictB (m9 (VV pq.1) (VV pq.2)) fun u =>
    bAnd(Nat.beq (m9 u (m9 u u)) I, bIf(Nat.beq u I, false, true))

theorem ch12648ord : Nat.beq (m9 X (m9 X X)) I = true ∧ Nat.beq (m9 Z (m9 Z Z)) I = true := by
  constructor <;> decide +kernel

theorem ch12648vv : CFSG.KC.LQT.P.allN 18 (fun i => CFSG.KS.Prim.canonK 315 9 (mask 9) (315 * 9)
    (VV i)) = true := by decide +kernel

theorem ch12648orb : orbB = true := by decide +kernel

theorem ch12648pair : (pairA.map pairB) == [true, true, true] := by decide +kernel

theorem ch12648words : ((List.range 4).map fun s => bAnd(Nat.beq (evW (wordA.getD s [])) (AB 0),
    Nat.beq (evW (wordB.getD s [])) (AB 1))) == [true, true, true, true] := by decide +kernel

theorem ch12648smallNeg :
    (CFSG.KC.LQT.P.allN 6 fun j => CFSG.KC.LQT.P.allN 3 fun p => CFSG.KC.LQT.P.allN 3 fun q =>
      CFSG.KC.LQT.P.anyN 3 fun e => Nat.beq (conjE (nIf(Nat.blt j (nat_lit 3), X, Z))
        (VV (Nat.add (Nat.mul 3 j) p)) e) (VV (Nat.add (Nat.mul 3 j) q))) = false ∧
    Nat.beq (evW (wordA.getD 0 [])) (AB 1) = false := by
  constructor <;> decide +kernel

end CertificateChecks.KernelJ2Sig
