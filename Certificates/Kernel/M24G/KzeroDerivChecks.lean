module

public import Certificates.Data.Kernel.M24G.KzeroDeriv
public import Certificates.Kernel.M24G.KzeroData
public import Certificates.Kernel.M24G.KzeroDerivData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.KzeroC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem kzDerivAll_ok : kzDerivAllF (Native.kzeroHs ()) KzeroD.kL KzeroDD.kD = true := by
  decide +kernel

theorem kzeroUFix_ok : kzeroUFixF = true := by
  decide +kernel

end CFSG.KC.M24G.KzeroC
