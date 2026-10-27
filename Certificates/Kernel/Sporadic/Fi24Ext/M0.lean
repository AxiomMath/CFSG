module

public import Certificates.Kernel.Sporadic.Fi24Ext.Data
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Fi24Ext

@[expose] def inv (j : Nat) : Bool := Nat.beq (CFSG.KD.BrFi24.MUL (G j) (Gi j)) CFSG.KD.BrFi24.ONE

theorem b2 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB (nat_lit 24))
    (CFSG.KD.BrFi24.RB (nat_lit 24))) B2 = true := by quickRfl

theorem rf : Nat.beq (CFSG.KD.BrFi24.MUL Rr F) RF = true := by quickRfl

theorem kk : Nat.beq (CFSG.KD.BrFi24.MUL RF CFSG.KD.Fi24Fix.R) K = true := by quickRfl

theorem sk : Nat.beq (CFSG.KD.BrFi24.MUL S K) E253 = true := by quickRfl

theorem ks : Nat.beq (CFSG.KD.BrFi24.MUL K S) E253 = true := by quickRfl

theorem es : Nat.beq (CFSG.KD.BrFi24.MUL E253 S) S = true := by quickRfl

theorem se : Nat.beq (CFSG.KD.BrFi24.MUL S E253) S = true := by quickRfl

theorem srf : Nat.beq (CFSG.KD.BrFi24.MUL S RF) SRF = true := by quickRfl

theorem ee : Nat.beq (CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Fix.R SRF) E = true := by quickRfl

theorem tt : Nat.beq (CFSG.KC.Fi24Ext.addM3 (nat_lit 609961) CFSG.KD.BrFi24.LO CFSG.KD.BrFi24.ONE E)
    T = true := by quickRfl

end CFSG.KD.Fi24Ext

#kc_each_unfold CFSG.KD.Fi24Ext.inv 0 13

end
