module

public import Certificates.Data.Kernel.L5.Eng0D
public import CFSG.GH74.GLS.C3.Layer2.L5C2fTableInputs
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.E0

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD.L5

theorem r1_chk :
    (elemsI sh0D.n).all (fun u => isR1 u == r1P.testBit u.v) = true := by
  kc_decide_fv

theorem post0 : postB r1P eng = true := by
  decide +kernel

end CFSG.KD.L5.E0

end
