module

public import Certificates.Kernel.He7222.ClsK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def nvK (ss : List Nat) : Bool :=
  strictB (keyF 14 (evK 14 (mask 14) ss) 5) (fun ks =>
  strictB (keyF 14 (fun p => pg 14 (mask 14) (HG.F 0) (evK 14 (mask 14) ss p)) 5) (fun kts =>
  strictB (keyF 14 (pg 14 (mask 14) (HG.F 0)) 5) (fun kt =>
  strictB (keyF 14 (fun p => pg 14 (mask 14) (getS scH 2)
      (evK 14 (mask 14) ss (pg 14 (mask 14) (getS scHI 2) p))) 5) (fun khs =>
    (Nat.beq khs kt || Nat.beq khs ks || Nat.beq khs kts) &&
    ((Nat.beq (getS (getLs a0CKeys 4) 0) ks && Nat.beq (getS (getLs a0CKeys 4) 1) kts) ||
      (Nat.beq (getS (getLs a0CKeys 4) 0) kts && Nat.beq (getS (getLs a0CKeys 4) 1) ks)) &&
    Nat.beq (lenS (getLs a0CKeys 4)) 2))))

theorem ch7222nv : nvK (stkK a0Ts (getLs a0RT 4)) = true := by quickRfl

end CFSG.KD.He7222

end
