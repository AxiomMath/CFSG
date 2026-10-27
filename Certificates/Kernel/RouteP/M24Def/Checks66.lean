module

public import Certificates.Kernel.RouteP.M24Def.Data
public import Certificates.Data.Kernel.RouteP.M24Def
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelM24Def

open CFSG.KC.M24Def

set_option maxRecDepth 400000

theorem ch450210k6 : Nat.beq (runE LD LI GQ FP RW (CB 66) 0 114 0) (CK 6) = true := by quickRfl

theorem ch450210k7 : Nat.beq (runE LD LI GQ FP RW (CB 66) 114 114 0) (CK 7) = true := by quickRfl

theorem ch450210k8 : Nat.beq (runE LD LI GQ FP RW (CB 66) 228 114 0) (CK 8) = true := by quickRfl

theorem ch450210k9 : Nat.beq (runE LD LI GQ FP RW (CB 66) 342 114 0) (CK 9) = true := by quickRfl

theorem ch450210k10 : Nat.beq (runE LD LI GQ FP RW (CB 66) 456 113 0) (CK 10) = true := by
  quickRfl

theorem ch450210s66 : (Nat.beq (ln 24 (CB 66) 0) 569 && Nat.beq (Nat.xor (Nat.xor (CK 6) (CK 7))
    (Nat.xor (Nat.xor (CK 8) (CK 9)) (CK 10))) 0) = true := by quickRfl

end CertificateChecks.KernelM24Def

end
