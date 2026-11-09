module

public import Certificates.Data.Kernel.ModZCode
public import Certificates.Data.Kernel.ModZCodeData
public import Certificates.Data.Kernel.Z4Code

public section

namespace Certificates.Kernel.ModZ

open CFSG.KC.ModZCode CFSG.KC.Z4Code CFSG.KC.T10Code

@[expose] def dE8F (t k : Nat) : Nat :=
  Nat.land (Nat.shiftRight DT8 (Nat.add (Nat.mul 27 t) (Nat.mul 3 k))) 7

@[expose] def mulC8F (uv m n : Nat) : Nat :=
  let t := Nat.add (Nat.add (Nat.mod (Nat.div m 1024) 2) (Nat.mul 2 (Nat.mod (Nat.div m 2048) 2)))
    (Nat.mul 4 (Nat.mod (Nat.div m 4096) 2))
  let w := if Nat.mod (Nat.div m 512) 2 = 0 then 1 else uv
  let q0 := Nat.mod n 8
  let q1 := Nat.mod (Nat.div n 8) 8
  let q2 := Nat.mod (Nat.div n 64) 8
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mod (Nat.add (Nat.mod m 8) (Nat.mul w (Nat.add (Nat.add (Nat.mul (dE8F t 0) q0)
      (Nat.mul (dE8F t 1) q1)) (Nat.mul (dE8F t 2) q2)))) 8)
    (Nat.mul 8 (Nat.mod (Nat.add (Nat.mod (Nat.div m 8) 8) (Nat.mul w (Nat.add (Nat.add
      (Nat.mul (dE8F t 3) q0) (Nat.mul (dE8F t 4) q1)) (Nat.mul (dE8F t 5) q2)))) 8)))
    (Nat.mul 64 (Nat.mod (Nat.add (Nat.mod (Nat.div m 64) 8) (Nat.mul w (Nat.add (Nat.add
      (Nat.mul (dE8F t 6) q0) (Nat.mul (dE8F t 7) q1)) (Nat.mul (dE8F t 8) q2)))) 8)))
    (Nat.mul 512 (Nat.mod (Nat.add (Nat.mod (Nat.div m 512) 2) (Nat.mod (Nat.div n 512) 2)) 2)))
    (Nat.mul 1024 (Nat.mod (Nat.add (Nat.mod (Nat.div m 1024) 2) (Nat.mod (Nat.div n 1024) 2)) 2)))
    (Nat.mul 2048 (Nat.mod (Nat.add (Nat.add (Nat.mod (Nat.div m 2048) 2)
      (Nat.mod (Nat.div n 2048) 2)) (Nat.mul (Nat.mod (Nat.div m 1024) 2)
        (Nat.mod (Nat.div n 4096) 2))) 2)))
    (Nat.mul 4096 (Nat.mod (Nat.add (Nat.mod (Nat.div m 4096) 2) (Nat.mod (Nat.div n 4096) 2)) 2))

theorem mulC8F_eq (uv : Nat) : mulC8 uv = mulC8F uv := rfl

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

theorem ch36407Mm : allF1 (mulC8 7) 8192 (2 ^ 8) 8 512 W8m = true := by
  rw [mulC8F_eq]
  decide +kernel

theorem ch36407M2m :
    allR (fun b => allR (F2 (mulC8 7) 8192 inM8c inA8c R8c (lane R8mT) (lane G8mT) (lane H8mT))
      (Nat.mul 128 b) 128) 0 64 = true := by decide +kernel

theorem ch36407Mt : allF1 (mulC8 3) 8192 (2 ^ 8) 8 512 W8t = true := by
  rw [mulC8F_eq]
  decide +kernel

theorem ch36407M2t :
    allR (fun b => allR (F2 (mulC8 3) 8192 inM8c inA8c R8c (lane R8tT) (lane G8tT) (lane H8tT))
      (Nat.mul 128 b) 128) 0 64 = true := by decide +kernel

end Certificates.Kernel.ModZ
