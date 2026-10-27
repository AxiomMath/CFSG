module

public import Certificates.Data.Kernel.L5.Sh1EngD
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh1

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus
  CFSG.KD.L5

theorem key1 : keyChk 128 Sh1R.C Sh1R.K 7 0 6 = true := by
  decide +kernel

theorem inv1_chk : invChkB 128 Sh1R.C Sh1R.K 7 0 6 Sh1R.I 0 = true := by
  decide +kernel


theorem embL1_chk :
    allT5L.all (fun t => decide (cget Sh1R.C 64 (embL1 t).v = codeP16 (embHom1 t).1)) = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh1

end
