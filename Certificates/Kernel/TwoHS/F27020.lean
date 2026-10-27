module

public import Certificates.Kernel.TwoHS.Har
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.LQT.C4126
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def fxR (i : Fin 4) : Nat := HC.F ([5, 12, 21, 34].getD i.val 0)

@[expose] noncomputable def sel2 (a0 a1 : Nat) (j : Fin 2) : Nat := nIf(Nat.beq j.val 0, a0, a1)

@[expose] noncomputable def sel6 (a0 a1 a2 a3 a4 a5 : Nat) (j : Fin 6) : Nat :=
  nIf(Nat.beq j.val 0, a0, nIf(Nat.beq j.val 1, a1, nIf(Nat.beq j.val 2, a2,
    nIf(Nat.beq j.val 3, a3, nIf(Nat.beq j.val 4, a4, a5)))))

@[expose] noncomputable def sel4 (a0 a1 a2 a3 : Nat) (l : Fin 4) : Nat :=
  nIf(Nat.beq l.val 0, a0, nIf(Nat.beq l.val 1, a1, nIf(Nat.beq l.val 2, a2, a3)))

@[expose] noncomputable def sel16 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Nat)
    (m : Fin 16) : Nat :=
  nIf(Nat.blt m.val 8,
    nIf(Nat.blt m.val 4,
      nIf(Nat.blt m.val 2, nIf(Nat.beq m.val 0, a0, a1), nIf(Nat.beq m.val 2, a2, a3)),
      nIf(Nat.blt m.val 6, nIf(Nat.beq m.val 4, a4, a5), nIf(Nat.beq m.val 6, a6, a7))),
    nIf(Nat.blt m.val 12,
      nIf(Nat.blt m.val 10, nIf(Nat.beq m.val 8, a8, a9), nIf(Nat.beq m.val 10, a10, a11)),
      nIf(Nat.blt m.val 14, nIf(Nat.beq m.val 12, a12, a13), nIf(Nat.beq m.val 14, a14, a15))))

@[expose] noncomputable def bind2 (f : Fin 2 → Nat) (k : (Fin 2 → Nat) → Bool) : Bool :=
  strictB (f 0) fun a0 => strictB (f 1) fun a1 => k (sel2 a0 a1)

@[expose] noncomputable def bind6 (f : Fin 6 → Nat) (k : (Fin 6 → Nat) → Bool) : Bool :=
  strictB (f 0) fun a0 => strictB (f 1) fun a1 => strictB (f 2) fun a2 =>
  strictB (f 3) fun a3 => strictB (f 4) fun a4 => strictB (f 5) fun a5 =>
    k (sel6 a0 a1 a2 a3 a4 a5)

@[expose] noncomputable def bind4 (f : Fin 4 → Nat) (k : (Fin 4 → Nat) → Bool) : Bool :=
  strictB (f 0) fun a0 => strictB (f 1) fun a1 => strictB (f 2) fun a2 => strictB (f 3) fun a3 =>
    k (sel4 a0 a1 a2 a3)

@[expose] noncomputable def bind16 (f : Fin 16 → Nat) (k : (Fin 16 → Nat) → Bool) : Bool :=
  strictB (f 0) fun a0 => strictB (f 1) fun a1 => strictB (f 2) fun a2 => strictB (f 3) fun a3 =>
  strictB (f 4) fun a4 => strictB (f 5) fun a5 => strictB (f 6) fun a6 => strictB (f 7) fun a7 =>
  strictB (f 8) fun a8 => strictB (f 9) fun a9 => strictB (f 10) fun a10 =>
  strictB (f 11) fun a11 => strictB (f 12) fun a12 => strictB (f 13) fun a13 =>
  strictB (f 14) fun a14 => strictB (f 15) fun a15 =>
    k (sel16 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)

@[expose] noncomputable def prodK (E : Fin 4 → Nat) (m : Nat) : Nat :=
  (List.finRange 4).foldl (fun acc l => cond (m.testBit l.val) (pc acc (E l)) acc) idK

@[expose] noncomputable def inv3 (p r : Nat) : Bool := invEqK 3850 12 (mask 12) (3850 * 12) p r

@[expose] noncomputable def ck3Body (i : Fin 4) (X : Fin 6 → Nat) (R : Nat) : Bool :=
  bAnd(inv3 R R, (List.finRange 6).all (fun j => Nat.beq (EV3 X X (hfxW i j))
    (CFSG.KS.HSAutN.pc (CFSG.KS.HSAutN.pc R (X j)) R)))

@[expose] noncomputable def ck27020R : Bool :=
  bind2 A3 fun A => bind2 A3I fun AI =>
  bind6 (fun j => EV3 A AI (hsGenWords.getD j.val [])) fun X =>
  bAnd((List.finRange 6).all (fun j => inv3 (X j) (X j)),
    (List.finRange 4).all fun i => strictB (fxR i) fun R => ck3Body i X R)

@[expose] noncomputable def dist16 (P : Fin 16 → Nat) : Bool :=
  (List.finRange 16).all fun a => (List.finRange 16).all fun b =>
    (a == b || !Nat.beq (P a) (P b))

end CFSG.KD.TwoHS

end
