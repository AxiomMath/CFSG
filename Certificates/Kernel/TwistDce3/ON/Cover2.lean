module

public import Certificates.Kernel.TwistDce3.ON.Data
public import Certificates.Kernel.TwistDce3.ON.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce3

set_option maxRecDepth 100000 in
theorem cover2 : coverRange 14 FO INVM RD RW 11172 4625 DS CV 6 1 = true := by
  decide +kernel

end CFSG.KD.ONDce3

end
