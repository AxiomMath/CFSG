module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Ext.Data
public import Certificates.Data.Kernel.Spor.Fi24Form

public section

namespace CFSG.KD.Fi24Form

open CFSG.KC.Fi24Form

@[expose] noncomputable def FA : Nat := CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Ext.F (CFSG.KD.BrFi24.RB 23)

@[expose] noncomputable def FB : Nat := CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Ext.F (CFSG.KD.BrFi24.RB 24)

@[expose] noncomputable def FBB : Nat := CFSG.KD.BrFi24.MUL FB (CFSG.KD.BrFi24.RB 24)

theorem f_sym0 : transM CFSG.KD.Fi24Ext.F CFSG.KD.Fi24Ext.F 0 196 4 = true := by quickRfl
theorem f_sym1 : transM CFSG.KD.Fi24Ext.F CFSG.KD.Fi24Ext.F 196 196 4 = true := by quickRfl
theorem f_sym2 : transM CFSG.KD.Fi24Ext.F CFSG.KD.Fi24Ext.F 392 196 4 = true := by quickRfl
theorem f_sym3 : transM CFSG.KD.Fi24Ext.F CFSG.KD.Fi24Ext.F 588 193 4 = true := by quickRfl

theorem fa_sym0 : transM FA FA 0 196 4 = true := by quickRfl
theorem fa_sym1 : transM FA FA 196 196 4 = true := by quickRfl
theorem fa_sym2 : transM FA FA 392 196 4 = true := by quickRfl
theorem fa_sym3 : transM FA FA 588 193 4 = true := by quickRfl

theorem fb_tr0 : transM FB FBB 0 196 4 = true := by quickRfl
theorem fb_tr1 : transM FB FBB 196 196 4 = true := by quickRfl
theorem fb_tr2 : transM FB FBB 392 196 4 = true := by quickRfl
theorem fb_tr3 : transM FB FBB 588 193 4 = true := by quickRfl

end CFSG.KD.Fi24Form

end
