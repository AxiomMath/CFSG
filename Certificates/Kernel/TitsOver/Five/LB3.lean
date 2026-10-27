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

theorem l_sl6000 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 6000 400 = true := by quickRfl
theorem l_sl6400 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 6400 400 = true := by quickRfl
theorem l_sl6800 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 6800 400 = true := by quickRfl
theorem l_sl7200 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 7200 400 = true := by quickRfl
theorem l_sl7600 : penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 PT) LE.T LE.PL
    LE.POS LE.SRT LE.SRI 7600 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Five

end
