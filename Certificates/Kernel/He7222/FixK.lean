module

public import Certificates.Data.Kernel.He7222.Fix
public import Certificates.Kernel.He7222.TabData
public import Certificates.Kernel.He7222.CovData
public import Certificates.Kernel.LocalComp.HeFix
public import CFSG.Certificates.Kernel.Common.Lce
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def a0Ts : List (List Nat) :=
  [a0T0, a0T1, a0T2, a0T3, a0T4, a0T5, a0T6, a0T7]

@[expose] noncomputable def t1Ts : List (List Nat) := [t1T0, t1T1, t1T2, t1T3, t1T4, t1T5, t1T6]

@[expose] noncomputable def rep0 (r : Nat) : Nat := tupK 8330 14 (mask 14) (pidn 8330 14) a0Ts (getLs a0RT r)

@[expose] noncomputable def rep1 (r : Nat) : Nat := tupK 8330 14 (mask 14) (pidn 8330 14) t1Ts (getLs t1RT r)

theorem ch7222fix0 : fixNeK 8330 14 (mask 14) (rep0 2) (HG.F 0) = true := by quickRfl

theorem ch7222fix1 : fixNeK 8330 14 (mask 14) (rep0 3) (HG.F 0) = true := by quickRfl

theorem ch7222fix2 : fixNeK 8330 14 (mask 14) (rep1 0) PT1 = true := by quickRfl

theorem ch7222fix3 : fixNeK 8330 14 (mask 14) (rep1 4) PT1 = true := by quickRfl

end CFSG.KD.He7222

end
