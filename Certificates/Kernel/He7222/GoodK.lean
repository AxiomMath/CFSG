module

public import Certificates.Data.Kernel.He7222.Good
public import Certificates.Kernel.He7222.FibK
public import Certificates.Kernel.He7222.GData
public import Certificates.Kernel.He7222.GWords
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def gdA (i : Nat) : Bool :=
  strictB (getS (getLs a0FI i) 0) (fun j => strictB (getS (getLs a0FI i) 1) (fun r =>
    goodLK 14 (mask 14) (getLL a0KTs j)
      (List.cons (getS scH j)
        (stkK a0Ts (getLs (getLL a0KC (getS a0SRep j)) (getS (getLs a0XR j) r))))
      (HG.F 0) LU LUI DW R5 R7 (getLL a0FT i) (getLL a0GD i)))

@[expose] noncomputable def gdT (i : Nat) : Bool :=
  strictB (getS (getLs t1FI i) 0) (fun j => strictB (getS (getLs t1FI i) 1) (fun r =>
    goodLK 14 (mask 14) (getLL t1KTs j)
      (List.cons (getS scH (Nat.add 3 j))
        (stkK t1Ts (getLs (getLL t1KC (getS t1SRep j)) (getS (getLs t1XR j) r))))
      PT1 LU LUI DW R5 R7 (getLL t1FT i) (getLL t1GD i)))

theorem ch7222gda : ∀ i < 10, gdA i = true := by kc_cover 2

theorem ch7222gdt : ∀ i < 44, gdT i = true := by kc_cover 4

theorem ch7222neggd : (CFSG.KC.notB (goodLK 14 (mask 14) (getLL a0KTs 0)
    (List.cons (getS scH 0) (stkK a0Ts (getLs (getLL a0KC (getS a0SRep 0)) (getS (getLs a0XR 0) 0))))
    (HG.F 0) LU LUI DW R5 R7 (getLL a0FT 0)
    (setLs (getLL a0GD 0) 0 [17, 0, 0, 0])) &&
  CFSG.KC.notB (goodLK 14 (mask 14) (getLL a0KTs 1)
    (List.cons (getS scH 1) (stkK a0Ts (getLs (getLL a0KC (getS a0SRep 1)) (getS (getLs a0XR 1) 0))))
    (HG.F 0) LU LUI DW R5 R7 (getLL a0FT 4)
    (setLs (getLL a0GD 4) 0 (setL (getLs (getLL a0GD 4) 0) 4 (Nat.add (getS (getLs (getLL a0GD 4) 0) 4) 1))))) =
    true := by
  quickRfl

end CFSG.KD.He7222

end
