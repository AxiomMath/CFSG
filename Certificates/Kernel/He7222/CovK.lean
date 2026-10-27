module

public import Certificates.Data.Kernel.He7222.Cover
public import Certificates.Kernel.He7222.Data
public import Certificates.Kernel.He7222.TabData
public import Certificates.Kernel.He7222.CovData
public import Certificates.Kernel.LocalComp.HeFix
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def cv0 (i : Nat) : Bool :=
  covK 14 (mask 14) 5 5 (HG.F 0) a0CKeys (getS a0Base 0) a0T0
    [a0T7, a0T6, a0T5, a0T4, a0T3, a0T2, a0T1] a0Cc a0Cov i

@[expose] noncomputable def cv1 (i : Nat) : Bool :=
  covK 14 (mask 14) 5 7 PT1 t1CKeys (getS t1Base 0) t1T0
    [t1T6, t1T5, t1T4, t1T3, t1T2, t1T1] t1Cc t1Cov i

theorem ch7222cov0 : ∀ i < 105, cv0 i = true := by kc_cover 8

theorem ch7222cov1 : ∀ i < 42, cv1 i = true := by kc_cover 8

end CFSG.KD.He7222

end
