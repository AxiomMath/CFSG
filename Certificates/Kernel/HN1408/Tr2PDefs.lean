module

public import Certificates.Kernel.HN1408.Tr2Defs
public import Certificates.Data.Kernel.Spor.BaseEq

public section

namespace CFSG.KD.HN1408.Tr2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.BaseEq

@[expose] noncomputable def t1PK (x1 x2 nS : Nat) (S T1 P1 : Nat → Nat) (j : Nat) : Bool :=
  strictB (T1 j) fun X => strictB (pt X x1) fun y1 => strictB (pt X x2) fun y2 =>
    bAnd(Nat.beq (pt X 0) 0,
      bAnd(allN j (fun j' => bIf(Nat.beq y1 (pt (T1 j') x1),
          bIf(Nat.beq y2 (pt (T1 j') x2), false, true), true)),
        bIf(Nat.beq j 0, true,
          strictB (P1 j) fun w => strictB (fd w 0) fun p => strictB (fd w 1) fun r =>
            bAnd(Nat.blt p j, bAnd(Nat.blt r nS, Nat.beq X (pc (S r) (T1 p)))))))

@[expose] noncomputable def cnt2 (n0 n1 : Nat) (T0 T1 : Nat → Nat) (F : Nat → Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => strictN ih fun a =>
      Nat.add a (strictN (T0 i) fun A => cntN n1 fun j => F A (T1 j))) n0

@[expose] noncomputable def comm2 (x A B H : Nat) : Bool :=
  bAnd(Nat.beq (pt A (pt B (pt H 0))) (pt H (pt A (pt B 0))),
    Nat.beq (pt A (pt B (pt H x))) (pt H (pt A (pt B x))))

end CFSG.KD.HN1408.Tr2

end
