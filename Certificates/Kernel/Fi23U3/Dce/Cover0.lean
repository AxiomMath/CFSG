module

public import Certificates.Kernel.Fi23U3.Dce.Data
public import Certificates.Kernel.Fi23U3.Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.Fi23Dce3

open CFSG.KC.TwDce3

set_option maxRecDepth 100000 in
theorem cover0 : coverRange 14 FO INVM RD RW 8748 44010 DS CV 0 5 = true := by
  decide +kernel

end CFSG.KD.Fi23Dce3

end
