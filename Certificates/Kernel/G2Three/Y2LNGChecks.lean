module

public import Certificates.Data.Kernel.G2Three.Y2LNG
public import Certificates.Kernel.G2Three.Rec

public section

namespace CFSG.KD.G2Three

set_option maxRecDepth 100000 in
theorem ngK_ok : ngCheckK GA = true := by decide +kernel

end CFSG.KD.G2Three

end
