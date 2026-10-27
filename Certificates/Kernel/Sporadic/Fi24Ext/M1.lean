module

public import Certificates.Kernel.Sporadic.Fi24Ext.Data
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Fi24Ext

@[expose] def cm (i : Nat) : Bool :=
  Nat.beq (CFSG.KD.BrFi24.MUL T (G (Nat.add i 2))) (CFSG.KD.BrFi24.MUL (G (Nat.add i 2)) T)

theorem n0 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL T (CFSG.KD.BrFi24.RB (nat_lit 23))) T)
    W0 = true := by quickRfl

theorem n1 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL T (CFSG.KD.BrFi24.RB (nat_lit 24))) T)
    W1 = true := by quickRfl

theorem p1 : Nat.beq (CFSG.KD.BrFi24.MUL T (CFSG.KD.BrFi24.MUL
    (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB (nat_lit 23)) T) (CFSG.KD.BrFi24.RB (nat_lit 23)))) P1 =
    true := by quickRfl

theorem p1sq : Nat.beq (CFSG.KD.BrFi24.MUL P1 P1) CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem p1ne : Bool.rec (motive := fun _ => Bool) true false (Nat.beq P1 CFSG.KD.BrFi24.ONE) = true := by
  quickRfl

theorem p2 : Nat.beq (CFSG.KD.BrFi24.MUL T (CFSG.KD.BrFi24.MUL
    (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB (nat_lit 24)) T) B2)) P2 = true := by quickRfl

theorem p2cb : Nat.beq (CFSG.KD.BrFi24.MUL P2 (CFSG.KD.BrFi24.MUL P2 P2)) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem p2ne : Bool.rec (motive := fun _ => Bool) true false (Nat.beq P2 CFSG.KD.BrFi24.ONE) = true := by
  quickRfl

end CFSG.KD.Fi24Ext

#kc_each_unfold CFSG.KD.Fi24Ext.cm 0 11

end
