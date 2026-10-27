module

public import Certificates.Kernel.Sporadic.Fi24Ext.Data
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Fi24Ext

@[expose] def vld (k : Nat) : Bool := CFSG.KD.BrFi24.VLD (MX k)

theorem vldA : CFSG.KD.BrFi24.VLD (CFSG.KD.BrFi24.RB (nat_lit 23)) = true := by quickRfl

theorem vldB : CFSG.KD.BrFi24.VLD (CFSG.KD.BrFi24.RB (nat_lit 24)) = true := by quickRfl

theorem vldRt : CFSG.KD.BrFi24.VLD CFSG.KD.Fi24Fix.R = true := by quickRfl

end CFSG.KD.Fi24Ext

#kc_each_unfold CFSG.KD.Fi24Ext.vld 0 94

end
