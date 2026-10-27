module

public import Certificates.Kernel.HN1408.ShIIDefs

public section

namespace CFSG.KD.HN1408

@[expose] def d8Mul (x y : Nat) : Nat :=
  if x < 4 then (if y < 4 then (x + y) % 4 else 4 + (y - x) % 4)
  else (if y < 4 then 4 + (x - 4 + y) % 4 else (y + 4 - x) % 4)

@[expose] def s3Ap (x k : Nat) : Nat :=
  if k = 0 then x % 3 else if k = 1 then x / 3 else 3 - x % 3 - x / 3

@[expose] def s3Mul (x y : Nat) : Nat := s3Ap x (s3Ap y 0) + 3 * s3Ap x (s3Ap y 1)

@[expose] def e2Mul (x y : Nat) : Nat := (x % 2 + y % 2) % 2 + 2 * ((x / 2 + y / 2) % 2)

@[expose] def t6Mul2 : Nat → Nat → Nat := prodMul 8 d8Mul s3Mul

@[expose] def t6Mul4 : Nat → Nat → Nat := prodMul 4 e2Mul d8Mul

@[expose] def t6Mul6 : Nat → Nat → Nat := prodMul 2 (zMul 2) d10Mul

@[expose] def t6Mul7 : Nat → Nat → Nat := prodMul 2 (zMul 2) d8Mul

end CFSG.KD.HN1408

end
