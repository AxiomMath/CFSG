module

public import Certificates.Kernel.Sporadic.OddCore.Co3Fus
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Fus

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem eE0 : penumSlK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt Co3E.T Co3E.PL
    Co3E.POS Co3E.SRT Co3E.SRI 0 128 = true := by quickRfl
theorem eE1 : penumSlK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt Co3E.T Co3E.PL
    Co3E.POS Co3E.SRT Co3E.SRI 128 128 = true := by quickRfl
theorem eE2 : penumSlK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt Co3E.T Co3E.PL
    Co3E.POS Co3E.SRT Co3E.SRI 256 128 = true := by quickRfl
theorem eE3 : penumSlK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt Co3E.T Co3E.PL
    Co3E.POS Co3E.SRT Co3E.SRI 384 128 = true := by quickRfl
theorem eE4 : penumSlK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt Co3E.T Co3E.PL
    Co3E.POS Co3E.SRT Co3E.SRI 512 128 = true := by quickRfl
theorem eE5 : penumSlK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt Co3E.T Co3E.PL
    Co3E.POS Co3E.SRT Co3E.SRI 640 128 = true := by quickRfl
theorem eE6 : penumSlK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt Co3E.T Co3E.PL
    Co3E.POS Co3E.SRT Co3E.SRI 768 128 = true := by quickRfl
theorem eE7 : penumSlK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt Co3E.T Co3E.PL
    Co3E.POS Co3E.SRT Co3E.SRI 896 128 = true := by quickRfl

theorem eH0 : slK Co3E.cnt (hsortPtK 276 9 (mask 9) Co3E.cnt Co3E.T Co3E.HS Co3E.HSI) 0 256 =
    true := by quickRfl
theorem eH1 : slK Co3E.cnt (hsortPtK 276 9 (mask 9) Co3E.cnt Co3E.T Co3E.HS Co3E.HSI) 256 256 =
    true := by quickRfl
theorem eH2 : slK Co3E.cnt (hsortPtK 276 9 (mask 9) Co3E.cnt Co3E.T Co3E.HS Co3E.HSI) 512 256 =
    true := by quickRfl
theorem eH3 : slK Co3E.cnt (hsortPtK 276 9 (mask 9) Co3E.cnt Co3E.T Co3E.HS Co3E.HSI) 768 256 =
    true := by quickRfl

theorem eCl0 : slK (Nat.mul Co3E.cnt 16)
    (findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 (Co3T.S) (Co3T.SI))) Co3ECl)
    0 2048 = true := by quickRfl
theorem eCl1 : slK (Nat.mul Co3E.cnt 16)
    (findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 (Co3T.S) (Co3T.SI))) Co3ECl)
    2048 2048 = true := by quickRfl
theorem eCl2 : slK (Nat.mul Co3E.cnt 16)
    (findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 (Co3T.S) (Co3T.SI))) Co3ECl)
    4096 2048 = true := by quickRfl
theorem eCl3 : slK (Nat.mul Co3E.cnt 16)
    (findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 (Co3T.S) (Co3T.SI))) Co3ECl)
    6144 2048 = true := by quickRfl
theorem eCl4 : slK (Nat.mul Co3E.cnt 16)
    (findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 (Co3T.S) (Co3T.SI))) Co3ECl)
    8192 2048 = true := by quickRfl
theorem eCl5 : slK (Nat.mul Co3E.cnt 16)
    (findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 (Co3T.S) (Co3T.SI))) Co3ECl)
    10240 2048 = true := by quickRfl
theorem eCl6 : slK (Nat.mul Co3E.cnt 16)
    (findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 (Co3T.S) (Co3T.SI))) Co3ECl)
    12288 2048 = true := by quickRfl
theorem eCl7 : slK (Nat.mul Co3E.cnt 16)
    (findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 (Co3T.S) (Co3T.SI))) Co3ECl)
    14336 2048 = true := by quickRfl

end CertificateChecks.KernelSpor.Co3Fus

end
