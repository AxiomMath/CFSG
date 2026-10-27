module

public import Certificates.Data.Kernel.M24G.FuseTodd
public import Certificates.Kernel.M24G.KzeroData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.FuseC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem fuseTodd_okF : fuseToddF (badMask (Native.octsS Native.baseSext)) KzeroD.kL = true := by
  decide +kernel

end CFSG.KC.M24G.FuseC
