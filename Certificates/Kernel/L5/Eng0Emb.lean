module

public import Certificates.Data.Kernel.L5.Eng0D
public import CFSG.GH74.GLS.C3.Layer2.L5C2fTableInputs
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.E0

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD.L5

theorem tC_chk : embT.map Prod.fst = Sh2FusT.embT.map Prod.fst := by
  decide +kernel

theorem embL_chk :
    allT5L.all (fun t => decide ((sh0D.idx (embHom0 t)).v = (embL t).v)) = true := by
  kc_decide_fv

end CFSG.KD.L5.E0

end
