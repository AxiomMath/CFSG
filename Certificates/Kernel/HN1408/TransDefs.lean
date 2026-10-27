module

public import Certificates.Kernel.HN1408.M11Defs

public section

namespace CFSG.KD.HN1408.Trans

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def sel7 (A0 A1 A2 A3 A4 A5 A6 j : Nat) : Nat :=
  nIf(Nat.beq j 0, A0, nIf(Nat.beq j 1, A1, nIf(Nat.beq j 2, A2, nIf(Nat.beq j 3, A3,
    nIf(Nat.beq j 4, A4, nIf(Nat.beq j 5, A5, A6))))))

@[expose] noncomputable def rowT (TR : Nat → Nat) (A0 A1 A2 A3 A4 A5 A6 q : Nat) : Bool :=
  strictB (TR q) fun w => strictB (f16 w 0) fun q' => strictB (f16 w 1) fun j =>
    bIf(Nat.beq q 0, Nat.beq (f16 w 2) 0,
      bAnd(Nat.blt q' 1408, bAnd(Nat.blt j 7, bAnd(Nat.beq (f16 w 2) (Nat.succ (f16 (TR q') 2)),
        Nat.beq (pt (sel7 A0 A1 A2 A3 A4 A5 A6 j) q') q))))

@[expose] noncomputable def transK (TR : Nat → Nat) : Bool :=
  strictB (WK [1]) fun A0 => strictB (WK [2]) fun A1 => strictB (WK [3]) fun A2 =>
    strictB (WK [4]) fun A3 => strictB (WK [5]) fun A4 => strictB (WK [6]) fun A5 =>
      strictB (WK [7]) fun A6 => allN 1408 fun q => rowT TR A0 A1 A2 A3 A4 A5 A6 q

end CFSG.KD.HN1408.Trans

end
