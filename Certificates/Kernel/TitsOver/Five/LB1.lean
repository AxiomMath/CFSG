module

public import Certificates.Kernel.TitsOver.Five.LEnum
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Data.Kernel.TitsOver.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TitsOver
open CertificateChecks.KernelMaxD2.TitsD (PT)

theorem l_sl2000 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 2000 400 = true := by quickRfl
theorem l_sl2400 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 2400 400 = true := by quickRfl
theorem l_sl2800 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 2800 400 = true := by quickRfl
theorem l_sl3200 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 3200 400 = true := by quickRfl
theorem l_sl3600 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 3600 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Five

end
