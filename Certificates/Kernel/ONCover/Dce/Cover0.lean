module

public import Certificates.Kernel.ONCover.Dce.Data
public import Certificates.Kernel.ONCover.Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.CoverSalt

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce3

set_option maxRecDepth 100000 in
theorem cover0 : coverRangeS 14 FO INVM RD RW 11172 18934 DS CV 0 4 = true := by
  decide +kernel

end CFSG.KD.ONCoverDce3

end
