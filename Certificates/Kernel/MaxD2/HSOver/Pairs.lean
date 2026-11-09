module

public import Certificates.Kernel.MaxD2.HSOver.Enum
public import Certificates.Kernel.MaxD2.HSOver.Data
public import Certificates.Data.Kernel.MaxD2.Pair
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.HSOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

@[expose] noncomputable def pairsK (lo m : Nat) : Bool :=
  allN m (fun d => allN (Nat.add lo d) (fun i => pairK 100 7 3 21 NE.cnt (r32 PT) NE.T FS KS REP
    REPI RB2 H2 (Nat.add (Nat.div (Nat.mul (Nat.add lo d) (Nat.sub (Nat.add lo d) 1)) 2) i) i
    (Nat.add lo d)))

theorem k_pair0 : pairsK 1 5 = true := by quickRfl
theorem k_pair1 : pairsK 6 5 = true := by quickRfl
theorem k_pair2_q : ∀ d < 4, allN (Nat.add 11 d) (fun i => pairK 100 7 3 21 NE.cnt (r32 PT) NE.T
    FS KS REP REPI RB2 H2 (Nat.add (Nat.div (Nat.mul (Nat.add 11 d) (Nat.sub (Nat.add 11 d) 1)) 2)
      i) i (Nat.add 11 d)) = true := by
  kc_cover 1

theorem k_pair2 : pairsK 11 4 = true := by
  unfold pairsK
  exact PK.allN_iff.2 k_pair2_q

end CertificateChecks.KernelMaxD2.HSOver

end
