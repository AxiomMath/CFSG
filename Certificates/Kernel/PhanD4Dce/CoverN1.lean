module

public import Certificates.Kernel.PhanD4Dce.CoverNData

set_option maxRecDepth 200000

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce3

theorem coverN1 : coverRangeN 15 FO INVM RD RW NS 15 12 22680 16625 DS CR CA 33 29 = true := by
  decide +kernel

end CFSG.KD.PhanD4Dce

end
