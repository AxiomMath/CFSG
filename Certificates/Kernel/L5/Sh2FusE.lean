module

public import Certificates.Data.Kernel.L5.Sh2FusT
public import CFSG.GH74.GLS.C3.Layer2.L5C5g
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh2Fus

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD.L5

theorem tC_chk : allT5L.map (fun t : ↥T5 => codeP t.1) = Sh2FusT.embT.map Prod.fst := by
  decide +kernel

theorem f5C_chk : F5list.map (fun g => (codeP g, codeP g⁻¹)) = Sh2FusT.f5C := by
  decide +kernel

theorem embL_chk : (List.finRange 4).all (fun ty => allT5L.all (fun t =>
    decide (((sh2TabD ty).idx (inc ty (embHom0 t))).v = (embL t).v))) = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh2Fus

end
