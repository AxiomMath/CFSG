module

public import Certificates.Kernel.TitsOver.Three.Loc1Data
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem c1n_sl0 : penumSlK 1755 11 (mask 11) (1755 * 11) false C1NE.G C1NE.GI C1NE.k C1NE.cnt C1NE.T
    C1NE.PL C1NE.POS C1NE.SRT C1NE.SRI 0 108 = true := by quickRfl
theorem c1n_sl108 : penumSlK 1755 11 (mask 11) (1755 * 11) false C1NE.G C1NE.GI C1NE.k C1NE.cnt
    C1NE.T C1NE.PL C1NE.POS C1NE.SRT C1NE.SRI 108 108 = true := by quickRfl
theorem c1n_sl216 : penumSlK 1755 11 (mask 11) (1755 * 11) false C1NE.G C1NE.GI C1NE.k C1NE.cnt
    C1NE.T C1NE.PL C1NE.POS C1NE.SRT C1NE.SRI 216 108 = true := by quickRfl
theorem c1n_sl324 : penumSlK 1755 11 (mask 11) (1755 * 11) false C1NE.G C1NE.GI C1NE.k C1NE.cnt
    C1NE.T C1NE.PL C1NE.POS C1NE.SRT C1NE.SRI 324 108 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
