module

public import Certificates.Kernel.UnitarySix.Sec3.C3606a
public import Certificates.Kernel.UnitarySix.Sec3.C3606b
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KS CFSG.KS.Prim CFSG.KC.Enum
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem k3606Run_four {lo : ℕ} (h : ∀ j < 4, k3606Run (lo + j) 1 = true) :
    k3606Run lo 4 = true := by
  refine allN_of_forall fun j hj => ?_
  have := allN_spec (h j hj) 0 Nat.one_pos
  rwa [Nat.add_zero] at this

theorem k3606_loop : prodLazyK 693 (693 * 10) CK1.LR CK1.TR k3606L 3 0 [] = true := by
  refine k3606_all fun s hs => k3606Run_four fun j hj => ?_
  rcases Nat.lt_or_ge (s * 4 + j) 60 with h | h
  · exact CFSG.KC.MiscCoset.Act.allR_spec kHa _ (Nat.zero_le _) (by omega)
  · exact CFSG.KC.MiscCoset.Act.allR_spec kHb _ h (by omega)

end CertificateChecks.KernelU6.Sec3
