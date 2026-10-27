module

public import Certificates.Data.Kernel.L5.Eng0D
public import CFSG.GH74.GLS.C3.Layer2.L5C2fInputs
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.E0

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD.L5

theorem codes_chk :
    codesChk (fun m : ↥Sh0 => m.1) sh0M codesP = true := by
  kc_decide_fv

theorem key_chk : keyChk 128 codesP keyP 7 0 6 = true := by
  decide +kernel

theorem inv_chk : invChkB 128 codesP keyP 7 0 6 invP 0 = true := by
  decide +kernel

end CFSG.KD.L5.E0

end
