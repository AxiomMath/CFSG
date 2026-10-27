
module

public import Certificates.Kernel.Sporadic.OddCore.J2CnK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Cn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem syE : penumSlK 315 9 (mask 9) (315 * 9) true J2SY.G J2SY.GI 8 J2SY.cnt J2SY.T J2SY.PL
    J2SY.POS J2SY.SRT J2SY.SRI 0 256 = true := by quickRfl
theorem k1E : penumSlK 315 9 (mask 9) (315 * 9) true J2K1.G J2K1.GI 3 J2K1.cnt J2K1.T J2K1.PL
    J2K1.POS J2K1.SRT J2K1.SRI 0 336 = true := by quickRfl
theorem q1aE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q1a.G J2Q1a.GI 3 J2Q1a.cnt J2Q1a.T J2Q1a.PL
    J2Q1a.POS J2Q1a.SRT J2Q1a.SRI 0 J2Q1a.cnt = true := by quickRfl
theorem q1bE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q1b.G J2Q1b.GI 3 J2Q1b.cnt J2Q1b.T J2Q1b.PL
    J2Q1b.POS J2Q1b.SRT J2Q1b.SRI 0 J2Q1b.cnt = true := by quickRfl
theorem q2aE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q2a.G J2Q2a.GI 5 J2Q2a.cnt J2Q2a.T J2Q2a.PL
    J2Q2a.POS J2Q2a.SRT J2Q2a.SRI 0 J2Q2a.cnt = true := by quickRfl
theorem q2bE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q2b.G J2Q2b.GI 5 J2Q2b.cnt J2Q2b.T J2Q2b.PL
    J2Q2b.POS J2Q2b.SRT J2Q2b.SRI 0 J2Q2b.cnt = true := by quickRfl
theorem q2cE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q2c.G J2Q2c.GI 5 J2Q2c.cnt J2Q2c.T J2Q2c.PL
    J2Q2c.POS J2Q2c.SRT J2Q2c.SRI 0 J2Q2c.cnt = true := by quickRfl
theorem q3aE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q3a.G J2Q3a.GI 4 J2Q3a.cnt J2Q3a.T J2Q3a.PL
    J2Q3a.POS J2Q3a.SRT J2Q3a.SRI 0 J2Q3a.cnt = true := by quickRfl
theorem q3bE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q3b.G J2Q3b.GI 4 J2Q3b.cnt J2Q3b.T J2Q3b.PL
    J2Q3b.POS J2Q3b.SRT J2Q3b.SRI 0 J2Q3b.cnt = true := by quickRfl
theorem q3cE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q3c.G J2Q3c.GI 4 J2Q3c.cnt J2Q3c.T J2Q3c.PL
    J2Q3c.POS J2Q3c.SRT J2Q3c.SRI 0 J2Q3c.cnt = true := by quickRfl
theorem e2aE : penumSlK 315 9 (mask 9) (315 * 9) true J2E2a.G J2E2a.GI 2 J2E2a.cnt J2E2a.T J2E2a.PL
    J2E2a.POS J2E2a.SRT J2E2a.SRI 0 J2E2a.cnt = true := by quickRfl
theorem e2bE : penumSlK 315 9 (mask 9) (315 * 9) true J2E2b.G J2E2b.GI 2 J2E2b.cnt J2E2b.T J2E2b.PL
    J2E2b.POS J2E2b.SRT J2E2b.SRI 0 J2E2b.cnt = true := by quickRfl

theorem syH : slK J2SY.cnt (hsortPtK 315 9 (mask 9) J2SY.cnt J2SY.T J2SY.HS J2SY.HSI)
    0 J2SY.cnt = true := by quickRfl
theorem k1H : slK J2K1.cnt (hsortPtK 315 9 (mask 9) J2K1.cnt J2K1.T J2K1.HS J2K1.HSI)
    0 J2K1.cnt = true := by quickRfl
theorem q1aH : slK J2Q1a.cnt (hsortPtK 315 9 (mask 9) J2Q1a.cnt J2Q1a.T J2Q1a.HS J2Q1a.HSI)
    0 J2Q1a.cnt = true := by quickRfl
theorem q1bH : slK J2Q1b.cnt (hsortPtK 315 9 (mask 9) J2Q1b.cnt J2Q1b.T J2Q1b.HS J2Q1b.HSI)
    0 J2Q1b.cnt = true := by quickRfl
theorem q2aH : slK J2Q2a.cnt (hsortPtK 315 9 (mask 9) J2Q2a.cnt J2Q2a.T J2Q2a.HS J2Q2a.HSI)
    0 J2Q2a.cnt = true := by quickRfl
theorem q2bH : slK J2Q2b.cnt (hsortPtK 315 9 (mask 9) J2Q2b.cnt J2Q2b.T J2Q2b.HS J2Q2b.HSI)
    0 J2Q2b.cnt = true := by quickRfl
theorem q2cH : slK J2Q2c.cnt (hsortPtK 315 9 (mask 9) J2Q2c.cnt J2Q2c.T J2Q2c.HS J2Q2c.HSI)
    0 J2Q2c.cnt = true := by quickRfl
theorem q3aH : slK J2Q3a.cnt (hsortPtK 315 9 (mask 9) J2Q3a.cnt J2Q3a.T J2Q3a.HS J2Q3a.HSI)
    0 J2Q3a.cnt = true := by quickRfl
theorem q3bH : slK J2Q3b.cnt (hsortPtK 315 9 (mask 9) J2Q3b.cnt J2Q3b.T J2Q3b.HS J2Q3b.HSI)
    0 J2Q3b.cnt = true := by quickRfl
theorem q3cH : slK J2Q3c.cnt (hsortPtK 315 9 (mask 9) J2Q3c.cnt J2Q3c.T J2Q3c.HS J2Q3c.HSI)
    0 J2Q3c.cnt = true := by quickRfl
theorem e2aH : slK J2E2a.cnt (hsortPtK 315 9 (mask 9) J2E2a.cnt J2E2a.T J2E2a.HS J2E2a.HSI)
    0 J2E2a.cnt = true := by quickRfl
theorem e2bH : slK J2E2b.cnt (hsortPtK 315 9 (mask 9) J2E2b.cnt J2E2b.T J2E2b.HS J2E2b.HSI)
    0 J2E2b.cnt = true := by quickRfl

theorem syCl0 : slK (Nat.mul J2SY.cnt 16)
    (findPtK J2SY.cnt J2SY.T (prodQK 315 9 (mask 9) 16 J2SY.T (bothK 8 (fun j => F (Nat.succ j))
      (fun j => I (Nat.succ j)))) J2SYCl) 0 2048 = true := by quickRfl
theorem syCl1 : slK (Nat.mul J2SY.cnt 16)
    (findPtK J2SY.cnt J2SY.T (prodQK 315 9 (mask 9) 16 J2SY.T (bothK 8 (fun j => F (Nat.succ j))
      (fun j => I (Nat.succ j)))) J2SYCl) 2048 2048 = true := by quickRfl

@[expose] noncomputable def scovK (i : Nat) : Bool :=
  strictB (J2SY.T i) (fun y => bIf(involK y, bIf(atK J2R1.cnt J2R1.T J2SYin1 i y, true,
    bIf(atK J2R2.cnt J2R2.T J2SYin2 i y, true, atK J2R3.cnt J2R3.T J2SYin3 i y)), true))

theorem k_scov : allN J2SY.cnt scovK = true := by quickRfl

@[expose] noncomputable def sel3K (i : Nat) : Bool :=
  strictB (J2C2.T i) (fun y => bIf(selK 3 5 y, bIf(atK J2Q3a.cnt J2Q3a.T J2C2in3a i y, true,
    bIf(atK J2Q3b.cnt J2Q3b.T J2C2in3b i y, true, atK J2Q3c.cnt J2Q3c.T J2C2in3c i y)), true))

theorem sel3_0 : slK J2C2.cnt sel3K 0 320 = true := by quickRfl
theorem sel3_1 : slK J2C2.cnt sel3K 320 320 = true := by quickRfl
theorem sel3_2 : slK J2C2.cnt sel3K 640 320 = true := by quickRfl
theorem sel3_3 : slK J2C2.cnt sel3K 960 320 = true := by quickRfl
theorem sel3_4 : slK J2C2.cnt sel3K 1280 320 = true := by quickRfl
theorem sel3_5 : slK J2C2.cnt sel3K 1600 320 = true := by quickRfl

end CertificateChecks.KernelSpor.J2Cn

end
