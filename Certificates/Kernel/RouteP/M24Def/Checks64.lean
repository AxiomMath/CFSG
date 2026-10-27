module

public import Certificates.Kernel.RouteP.M24Def.Data
public import Certificates.Data.Kernel.RouteP.M24Def
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelM24Def

open CFSG.KC.M24Def

set_option maxRecDepth 400000

theorem ch450210k0 : Nat.beq (runE LD LI GQ FP RW (CB 64) 0 130 0) (CK 0) = true := by quickRfl

theorem ch450210k1 : Nat.beq (runE LD LI GQ FP RW (CB 64) 130 130 0) (CK 1) = true := by quickRfl

theorem ch450210k2 : Nat.beq (runE LD LI GQ FP RW (CB 65) 0 117 0) (CK 2) = true := by quickRfl

theorem ch450210k3 : Nat.beq (runE LD LI GQ FP RW (CB 65) 117 117 0) (CK 3) = true := by quickRfl

theorem ch450210k4 : Nat.beq (runE LD LI GQ FP RW (CB 65) 234 117 0) (CK 4) = true := by quickRfl

theorem ch450210k5 : Nat.beq (runE LD LI GQ FP RW (CB 65) 351 116 0) (CK 5) = true := by quickRfl

theorem ch450210s64 : (Nat.beq (ln 24 (CB 64) 0) 260 && Nat.beq (Nat.xor (CK 0) (CK 1)) 0) = true :=
  by quickRfl

theorem ch450210s65 : (Nat.beq (ln 24 (CB 65) 0) 467 &&
    Nat.beq (Nat.xor (Nat.xor (CK 2) (CK 3)) (Nat.xor (CK 4) (CK 5))) 0) = true := by quickRfl

end CertificateChecks.KernelM24Def

end
