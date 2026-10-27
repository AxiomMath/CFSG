module

public import Certificates.Data.Kernel.ModZCode
public import Certificates.Data.Kernel.ModZCodeData
public import Certificates.Data.Kernel.Z4Code

public section

namespace Certificates.Kernel.ModZ

open CFSG.KC.ModZCode CFSG.KC.Z4Code CFSG.KC.T10Code

theorem ch36407SQ : Nat.beq SQ4 (sqMask mulC 1024) = true := by decide +kernel

theorem ch36407E0 : allR (FE mulC 1024 inE4c SQ4 (2 ^ 8)) 0 128 = true := by decide +kernel
theorem ch36407E1 : allR (FE mulC 1024 inE4c SQ4 (2 ^ 8)) 128 128 = true := by decide +kernel
theorem ch36407E2 : allR (FE mulC 1024 inE4c SQ4 (2 ^ 8)) 256 128 = true := by decide +kernel
theorem ch36407E3 : allR (FE mulC 1024 inE4c SQ4 (2 ^ 8)) 384 128 = true := by decide +kernel
theorem ch36407E4 : allR (FE mulC 1024 inE4c SQ4 (2 ^ 8)) 512 128 = true := by decide +kernel
theorem ch36407E5 : allR (FE mulC 1024 inE4c SQ4 (2 ^ 8)) 640 128 = true := by decide +kernel
theorem ch36407E6 : allR (FE mulC 1024 inE4c SQ4 (2 ^ 8)) 768 128 = true := by decide +kernel
theorem ch36407E7 : allR (FE mulC 1024 inE4c SQ4 (2 ^ 8)) 896 128 = true := by decide +kernel

theorem ch36407Ca : allF1 mulC 1024 (2 ^ 7) 4 64 W4a = true := by decide +kernel
theorem ch36407Cb : allF1 mulC 1024 (2 ^ 8) 8 64 W4b = true := by decide +kernel

theorem ch36407C2 :
    allR (fun b => allR (F2 mulC 1024 inM4c inA4c R4c (lane R4T) (lane G4T) (lane H4T))
      (Nat.mul 128 b) 128) 0 8 = true := by decide +kernel

theorem ch36407Mm : allF1 (mulC8 7) 8192 (2 ^ 8) 8 512 W8m = true := by decide +kernel

theorem ch36407M2m :
    allR (fun b => allR (F2 (mulC8 7) 8192 inM8c inA8c R8c (lane R8mT) (lane G8mT) (lane H8mT))
      (Nat.mul 128 b) 128) 0 64 = true := by decide +kernel

theorem ch36407Mt : allF1 (mulC8 3) 8192 (2 ^ 8) 8 512 W8t = true := by decide +kernel

theorem ch36407M2t :
    allR (fun b => allR (F2 (mulC8 3) 8192 inM8c inA8c R8c (lane R8tT) (lane G8tT) (lane H8tT))
      (Nat.mul 128 b) 128) 0 64 = true := by decide +kernel

end Certificates.Kernel.ModZ
