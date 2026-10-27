module

public import Certificates.Kernel.PhanD4Dce.Data
public import Certificates.Kernel.PhanD4Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce3

set_option maxRecDepth 200000 in
theorem omega_letters : lettersOK 15 FO INVM 12 22680 = true := by
  decide +kernel

end CFSG.KD.PhanD4Dce

end
