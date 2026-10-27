module

public import Certificates.Kernel.TitsOver.Three.Loc0Data
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem c0n_sl0 : penumSlK 1755 11 (mask 11) (1755 * 11) false C0NE.G C0NE.GI C0NE.k C0NE.cnt C0NE.T
    C0NE.PL C0NE.POS C0NE.SRT C0NE.SRI 0 108 = true := by quickRfl
theorem c0n_sl108 : penumSlK 1755 11 (mask 11) (1755 * 11) false C0NE.G C0NE.GI C0NE.k C0NE.cnt
    C0NE.T C0NE.PL C0NE.POS C0NE.SRT C0NE.SRI 108 108 = true := by quickRfl
theorem c0n_sl216 : penumSlK 1755 11 (mask 11) (1755 * 11) false C0NE.G C0NE.GI C0NE.k C0NE.cnt
    C0NE.T C0NE.PL C0NE.POS C0NE.SRT C0NE.SRI 216 108 = true := by quickRfl
theorem c0n_sl324 : penumSlK 1755 11 (mask 11) (1755 * 11) false C0NE.G C0NE.GI C0NE.k C0NE.cnt
    C0NE.T C0NE.PL C0NE.POS C0NE.SRT C0NE.SRI 324 108 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
