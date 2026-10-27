module

public import Certificates.Data.Kernel.He7222.Cls
public import Certificates.Kernel.He7222.FixK
public import Certificates.Kernel.He7222.Data
public import Certificates.Kernel.He7222.HData
public import Certificates.Kernel.He7222.InvData
public import Certificates.Kernel.He7222.ClsData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def a0TIs : List (List Nat) :=
  [a0TI0, a0TI1, a0TI2, a0TI3, a0TI4, a0TI5, a0TI6, a0TI7]

@[expose] noncomputable def t1TIs : List (List Nat) :=
  [t1TI0, t1TI1, t1TI2, t1TI3, t1TI4, t1TI5, t1TI6]

@[expose] noncomputable def ca (cl : Nat) : Bool :=
  clsK 14 (mask 14) a0Ts a0TIs (stkK a0Ts (getLs a0RT cl)) (getLL a0KC cl) (getLs a0CKeys cl)

@[expose] noncomputable def ct (cl : Nat) : Bool :=
  clsK 14 (mask 14) t1Ts t1TIs (stkK t1Ts (getLs t1RT cl)) (getLL t1KC cl) (getLs t1CKeys cl)

@[expose] noncomputable def sa (j : Nat) : Bool :=
  svK 14 (mask 14) a0Ts a0TIs (stkK a0Ts (getLs a0RT (getS a0SRep j))) (getS scH j) (getS scHI j)
    (HG.F 0) (getLL a0KC (getS a0SRep j)) (getLs a0Sv j)

@[expose] noncomputable def st (j : Nat) : Bool :=
  svK 14 (mask 14) t1Ts t1TIs (stkK t1Ts (getLs t1RT (getS t1SRep j))) (getS scH (Nat.add 3 j))
    (getS scHI (Nat.add 3 j)) PT1 (getLL t1KC (getS t1SRep j)) (getLs t1Sv j)

theorem ch7222ca0 : ca 0 = true := by quickRfl
theorem ch7222ca1 : ca 1 = true := by quickRfl
theorem ch7222ca2 : ca 2 = true := by quickRfl
theorem ch7222ca3 : ca 3 = true := by quickRfl
theorem ch7222ca4 : ca 4 = true := by quickRfl
theorem ch7222ct0 : ct 0 = true := by quickRfl
theorem ch7222ct1 : ct 1 = true := by quickRfl
theorem ch7222ct2 : ct 2 = true := by quickRfl
theorem ch7222ct3 : ct 3 = true := by quickRfl
theorem ch7222ct4 : ct 4 = true := by quickRfl
theorem ch7222ct5 : ct 5 = true := by quickRfl
theorem ch7222ct6 : ct 6 = true := by quickRfl

theorem ch7222sa0 : sa 0 = true := by quickRfl
theorem ch7222sa1 : sa 1 = true := by quickRfl
theorem ch7222st0 : st 0 = true := by quickRfl
theorem ch7222st1 : st 1 = true := by quickRfl
theorem ch7222st2 : st 2 = true := by quickRfl
theorem ch7222st3 : st 3 = true := by quickRfl
theorem ch7222st4 : st 4 = true := by quickRfl

end CFSG.KD.He7222

end
