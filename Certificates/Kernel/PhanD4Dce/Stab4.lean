module

public import Certificates.Kernel.PhanD4Dce.Data
public import Certificates.Kernel.PhanD4Dce.CoverData
public import Certificates.Kernel.PhanD4Dce.ChainData
public import Certificates.Data.Kernel.TwistDce3.ChainP

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce3

set_option maxRecDepth 200000 in
theorem stab4 : stabRangeP 12 F INVM 2160 RD RW 16625 DS CG CW CB CS CT CN 114 13 = true := by
  decide +kernel

end CFSG.KD.PhanD4Dce

end
