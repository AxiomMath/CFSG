module

public import Certificates.Kernel.He7222.FixK
public import Certificates.Kernel.He7222.Data
public import Certificates.Kernel.He7222.HData
public import Certificates.Kernel.He7222.HWords
public import CFSG.Certificates.Kernel.Common.Lce
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain
  CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def hK (j : Nat) : Bool :=
  wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (HW.getD j []) (getS scH j)

@[expose] noncomputable def cjK (h tau s : Nat) : Bool :=
  bAnd(canonK 8330 14 (mask 14) (Nat.mul 8330 14) s,
    Nat.beq (pcomp 8330 14 (mask 14) h tau) (pcomp 8330 14 (mask 14) s h))

theorem ch7222hlen : Nat.beq (lenS scH) 8 = true := by quickRfl
theorem ch7222h0 : hK 0 = true := by quickRfl
theorem ch7222h1 : hK 1 = true := by quickRfl
theorem ch7222h2 : hK 2 = true := by quickRfl
theorem ch7222h3 : hK 3 = true := by quickRfl
theorem ch7222h4 : hK 4 = true := by quickRfl
theorem ch7222h5 : hK 5 = true := by quickRfl
theorem ch7222h6 : hK 6 = true := by quickRfl
theorem ch7222h7 : hK 7 = true := by quickRfl

theorem ch7222cj0 : cjK (getS scH 0) (HG.F 0) (rep0 (getS a0SRep 0)) = true := by quickRfl
theorem ch7222cj1 : cjK (getS scH 1) (HG.F 0) (rep0 (getS a0SRep 1)) = true := by quickRfl
theorem ch7222cj2 : cjK (getS scH 2) (HG.F 0) (rep0 (getS a0SRep 2)) = true := by quickRfl
theorem ch7222cj3 : cjK (getS scH 3) PT1 (rep1 (getS t1SRep 0)) = true := by quickRfl
theorem ch7222cj4 : cjK (getS scH 4) PT1 (rep1 (getS t1SRep 1)) = true := by quickRfl
theorem ch7222cj5 : cjK (getS scH 5) PT1 (rep1 (getS t1SRep 2)) = true := by quickRfl
theorem ch7222cj6 : cjK (getS scH 6) PT1 (rep1 (getS t1SRep 3)) = true := by quickRfl
theorem ch7222cj7 : cjK (getS scH 7) PT1 (rep1 (getS t1SRep 4)) = true := by quickRfl

end CFSG.KD.He7222

end
