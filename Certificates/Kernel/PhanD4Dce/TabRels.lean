module

public import Certificates.Kernel.PhanD4Dce.Data
public import Certificates.Kernel.PhanD4Dce.A3Codes
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce3

set_option maxRecDepth 200000 in
theorem tab_letters : lettersOK 12 F INVM 12 2160 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem tab_rels : relsOK 12 F 2160 a3CodesL = true := by
  decide +kernel

end CFSG.KD.PhanD4Dce

end
