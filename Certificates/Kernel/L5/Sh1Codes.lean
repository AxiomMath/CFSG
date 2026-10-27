module

public import Certificates.Data.Kernel.L5.Sh1EngD
public import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs

public section

namespace CFSG.KD.L5.Sh1

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD.L5

theorem codes1 : codesChk Prod.fst sh1WW Sh1R.C = true := by
  decide +kernel

end CFSG.KD.L5.Sh1

end
