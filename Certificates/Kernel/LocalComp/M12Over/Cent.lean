module

public import Certificates.Kernel.LocalComp.M12Over.CentData
public import Certificates.Kernel.LocalComp.M12End.Facts
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.RankTwoSporadic.M12 CertificateChecks.KernelLC.M12End

theorem bC : (Nat.beq m12OverCW.size C.ng && allN C.ng fun k => bindArrK m12OverCW[k]! 24 5 (C.G k)) =
    true := by quickRfl
theorem pC : allN C.ng (fun k => permOK 24 5 (mask 5) (24 * 5) (C.G k)
    (pinvS 24 5 (mask 5) (C.G k))) = true := by quickRfl
theorem keyC : keysK 24 5 m12PS C.N C.T = true := by quickRfl

theorem setC : enumOK 24 m12OverCW m12PS (enumBfs 24 m12OverCW m12PS m12Fuel) = true ∧
    (∀ x, x ∈ (enumBfs 24 m12OverCW m12PS m12Fuel).pts ↔ ∃ i < C.N, unpack 24 5 (C.T i) = x) ∧
    (enumBfs 24 m12OverCW m12PS m12Fuel).pts.size = C.N :=
  enumBfs_of_bfsK_set (binds_of_check bC).1 (binds_of_check bC).2
    (fun k hk => allN_spec pC k hk) kId kPid C.ok m12PS_lt keyC (by decide)

theorem kCgen : allLt m12OverCW.size (fun i =>
    (inPA m12OverCW[i]! || inPA (compA 24 m12SigArr m12OverCW[i]!)) &&
      allLt m12E0.size fun j => m12CommA m12OverCW[i]! m12E0[j]!) = true := by quickRfl

theorem kC4 : allN C.N (fun i => !eqA 24 (m12PowA (unpack 24 5 (C.T i)) 4) (idA 24) ||
    eqA 24 (compA 24 (unpack 24 5 (C.T i)) (unpack 24 5 (C.T i))) (idA 24)) = true := by quickRfl

theorem centOK : m12OverCentOK m12S m12E0 m12OverCW = true := by
  obtain ⟨hok, hmem, hsz⟩ := setC
  unfold m12OverCentOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hok, ?_⟩, ?_⟩, ?_⟩
  · rw [hsz]
    decide +kernel
  · refine allLt_mono (fun i _ h => ?_) kCgen
    rw [Bool.and_eq_true] at h ⊢
    refine ⟨?_, h.2⟩
    rw [m12InR, Bool.or_eq_true]
    rw [Bool.or_eq_true] at h
    exact h.1.imp inPA_sound inPA_sound
  · exact allLt_pts (f := fun x => !eqA 24 (m12PowA x 4) (idA 24) || eqA 24 (compA 24 x x) (idA 24))
      hmem (fun i hi => allN_spec kC4 i hi)

theorem kH0 : inPA m12OverH0 = true := by quickRfl

theorem hOK : m12OverHOK m12S m12E0 m12OverH0 = true := by
  unfold m12OverHOK
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨by decide +kernel, inPA_sound kH0⟩, by decide +kernel⟩, by decide +kernel⟩

end CertificateChecks.KernelLC.M12Over

end
