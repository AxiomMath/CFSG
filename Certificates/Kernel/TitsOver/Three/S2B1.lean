module

public import Certificates.Kernel.TitsOver.Three.SEnum2
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Data.Kernel.TitsOver.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TitsOver
open CertificateChecks.KernelMaxD2.TitsD (PT)

theorem s2_sl3200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 3200 400 = true := by quickRfl
theorem s2_sl3600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 3600 400 = true := by quickRfl
theorem s2_sl4000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 4000 400 = true := by quickRfl
theorem s2_sl4400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 4400 400 = true := by quickRfl
theorem s2_sl4800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 4800 400 = true := by quickRfl
theorem s2_sl5200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 5200 400 = true := by quickRfl
theorem s2_sl5600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 5600 400 = true := by quickRfl
theorem s2_sl6000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 6000 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
