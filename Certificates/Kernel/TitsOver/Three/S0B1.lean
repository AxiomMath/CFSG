module

public import Certificates.Kernel.TitsOver.Three.SEnum0
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Data.Kernel.TitsOver.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TitsOver
open CertificateChecks.KernelMaxD2.TitsD (PT)

theorem s0_sl2800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6 (r32 PT) S0E.T
    S0E.PL S0E.POS S0E.SRT S0E.SRI 2800 400 = true := by quickRfl
theorem s0_sl3200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6 (r32 PT) S0E.T
    S0E.PL S0E.POS S0E.SRT S0E.SRI 3200 400 = true := by quickRfl
theorem s0_sl3600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6 (r32 PT) S0E.T
    S0E.PL S0E.POS S0E.SRT S0E.SRI 3600 400 = true := by quickRfl
theorem s0_sl4000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6 (r32 PT) S0E.T
    S0E.PL S0E.POS S0E.SRT S0E.SRI 4000 400 = true := by quickRfl
theorem s0_sl4400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6 (r32 PT) S0E.T
    S0E.PL S0E.POS S0E.SRT S0E.SRI 4400 400 = true := by quickRfl
theorem s0_sl4800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6 (r32 PT) S0E.T
    S0E.PL S0E.POS S0E.SRT S0E.SRI 4800 400 = true := by quickRfl
theorem s0_sl5200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6 (r32 PT) S0E.T
    S0E.PL S0E.POS S0E.SRT S0E.SRI 5200 400 = true := by quickRfl
theorem s0_sl5600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6 (r32 PT) S0E.T
    S0E.PL S0E.POS S0E.SRT S0E.SRI 5600 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
