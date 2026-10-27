
module

public import Certificates.Kernel.Sporadic.OddCore.J2CnK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Cn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem o1E0 : penumSlK 315 9 (mask 9) (315 * 9) true J2R1.G J2R1.GI 2 J2R1.cnt J2R1.T J2R1.PL
    J2R1.POS J2R1.SRT J2R1.SRI 0 450 = true := by quickRfl
theorem o1E1 : penumSlK 315 9 (mask 9) (315 * 9) true J2R1.G J2R1.GI 2 J2R1.cnt J2R1.T J2R1.PL
    J2R1.POS J2R1.SRT J2R1.SRI 450 450 = true := by quickRfl
theorem o1E2 : penumSlK 315 9 (mask 9) (315 * 9) true J2R1.G J2R1.GI 2 J2R1.cnt J2R1.T J2R1.PL
    J2R1.POS J2R1.SRT J2R1.SRI 900 450 = true := by quickRfl
theorem o1E3 : penumSlK 315 9 (mask 9) (315 * 9) true J2R1.G J2R1.GI 2 J2R1.cnt J2R1.T J2R1.PL
    J2R1.POS J2R1.SRT J2R1.SRI 1350 450 = true := by quickRfl
theorem o2E0 : penumSlK 315 9 (mask 9) (315 * 9) true J2R2.G J2R2.GI 2 J2R2.cnt J2R2.T J2R2.PL
    J2R2.POS J2R2.SRT J2R2.SRI 0 420 = true := by quickRfl
theorem o2E1 : penumSlK 315 9 (mask 9) (315 * 9) true J2R2.G J2R2.GI 2 J2R2.cnt J2R2.T J2R2.PL
    J2R2.POS J2R2.SRT J2R2.SRI 420 420 = true := by quickRfl
theorem o2E2 : penumSlK 315 9 (mask 9) (315 * 9) true J2R2.G J2R2.GI 2 J2R2.cnt J2R2.T J2R2.PL
    J2R2.POS J2R2.SRT J2R2.SRI 840 420 = true := by quickRfl
theorem o2E3 : penumSlK 315 9 (mask 9) (315 * 9) true J2R2.G J2R2.GI 2 J2R2.cnt J2R2.T J2R2.PL
    J2R2.POS J2R2.SRT J2R2.SRI 1260 420 = true := by quickRfl
theorem o2E4 : penumSlK 315 9 (mask 9) (315 * 9) true J2R2.G J2R2.GI 2 J2R2.cnt J2R2.T J2R2.PL
    J2R2.POS J2R2.SRT J2R2.SRI 1680 420 = true := by quickRfl
theorem o2E5 : penumSlK 315 9 (mask 9) (315 * 9) true J2R2.G J2R2.GI 2 J2R2.cnt J2R2.T J2R2.PL
    J2R2.POS J2R2.SRT J2R2.SRI 2100 420 = true := by quickRfl
theorem o3E : penumSlK 315 9 (mask 9) (315 * 9) true J2R3.G J2R3.GI 2 J2R3.cnt J2R3.T J2R3.PL
    J2R3.POS J2R3.SRT J2R3.SRI 0 315 = true := by quickRfl

theorem o1H0 : slK J2R1.cnt (hsortPtK 315 9 (mask 9) J2R1.cnt J2R1.T J2R1.HS J2R1.HSI) 0 900 =
    true := by quickRfl
theorem o1H1 : slK J2R1.cnt (hsortPtK 315 9 (mask 9) J2R1.cnt J2R1.T J2R1.HS J2R1.HSI) 900 900 =
    true := by quickRfl
theorem o2H0 : slK J2R2.cnt (hsortPtK 315 9 (mask 9) J2R2.cnt J2R2.T J2R2.HS J2R2.HSI) 0 840 =
    true := by quickRfl
theorem o2H1 : slK J2R2.cnt (hsortPtK 315 9 (mask 9) J2R2.cnt J2R2.T J2R2.HS J2R2.HSI) 840 840 =
    true := by quickRfl
theorem o2H2 : slK J2R2.cnt (hsortPtK 315 9 (mask 9) J2R2.cnt J2R2.T J2R2.HS J2R2.HSI) 1680 840 =
    true := by quickRfl
theorem o3H : slK J2R3.cnt (hsortPtK 315 9 (mask 9) J2R3.cnt J2R3.T J2R3.HS J2R3.HSI) 0 315 =
    true := by quickRfl

end CertificateChecks.KernelSpor.J2Cn

end
