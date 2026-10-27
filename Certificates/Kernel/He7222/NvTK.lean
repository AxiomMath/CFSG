module

public import Certificates.Data.Kernel.He7222.Nv
public import Certificates.Kernel.He7222.ClsK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def nvS : List Nat := stkK a0Ts (getLs a0RT 4)

@[expose] noncomputable def nvT (T TI : List Nat) : Bool :=
  nvLK 14 (mask 14) nvS (keyF 14 (evK 14 (mask 14) nvS) 5)
    (keyF 14 (fun p => pg 14 (mask 14) (HG.F 0) (evK 14 (mask 14) nvS p)) 5) T TI

theorem ch7222shr : Nat.beq (Nat.shiftRight (getS scH 2) (Nat.mul 8330 14)) 0 = true := by
  quickRfl

theorem ch7222nvt0: nvT a0T0 a0TI0 = true := by quickRfl
theorem ch7222nvt1 : nvT a0T1 a0TI1 = true := by quickRfl
theorem ch7222nvt2 : nvT a0T2 a0TI2 = true := by quickRfl
theorem ch7222nvt3 : nvT a0T3 a0TI3 = true := by quickRfl
theorem ch7222nvt4 : nvT a0T4 a0TI4 = true := by quickRfl
theorem ch7222nvt5 : nvT a0T5 a0TI5 = true := by quickRfl
theorem ch7222nvt6 : nvT a0T6 a0TI6 = true := by quickRfl
theorem ch7222nvt7 : nvT a0T7 a0TI7 = true := by quickRfl

end CFSG.KD.He7222

end
