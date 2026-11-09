module

public import Certificates.Kernel.Sporadic.Fi24P7.Defs
public import Certificates.Kernel.Sporadic.Fi24Fix.Split

public section

namespace CFSG.KD.Fi24P7

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24P7

theorem chStep_of {P : List (List Nat)} {b k i : Nat} {w : List Nat} {Y Z : Nat}
    (hw : CFSG.KC.Fi24Kn.nthW P i = w)
    (hY : nIf(Nat.blt (Nat.succ i) k, MX (Nat.add b (Nat.succ i)), CFSG.KD.BrFi24.ONE) = Y)
    (hZ : MX (Nat.add b i) = Z)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG w Y) Z = true) :
    chStep P b k i = true := by
  unfold chStep
  rw [hw, hY, hZ]
  exact h

end CFSG.KD.Fi24P7

end
