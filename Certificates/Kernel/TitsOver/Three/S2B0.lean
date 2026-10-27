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

theorem s2_sl0 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 0 400 = true := by quickRfl
theorem s2_sl400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 400 400 = true := by quickRfl
theorem s2_sl800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 800 400 = true := by quickRfl
theorem s2_sl1200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 1200 400 = true := by quickRfl
theorem s2_sl1600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 1600 400 = true := by quickRfl
theorem s2_sl2000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 2000 400 = true := by quickRfl
theorem s2_sl2400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 2400 400 = true := by quickRfl
theorem s2_sl2800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 2800 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
