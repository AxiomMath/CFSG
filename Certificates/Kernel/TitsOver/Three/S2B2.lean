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

theorem s2_sl6400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 6400 400 = true := by quickRfl
theorem s2_sl6800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 6800 400 = true := by quickRfl
theorem s2_sl7200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 7200 400 = true := by quickRfl
theorem s2_sl7600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 7600 400 = true := by quickRfl
theorem s2_sl8000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 8000 400 = true := by quickRfl
theorem s2_sl8400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 8400 400 = true := by quickRfl
theorem s2_sl8800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 8800 400 = true := by quickRfl
theorem s2_sl9200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6 (r32 PT) S2E.T
    S2E.PL S2E.POS S2E.SRT S2E.SRI 9200 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
