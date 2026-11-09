module

public import Certificates.Kernel.TwoHSLe4.S9W
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PCountSound

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelTwoHSLe4.S9

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.Enum

theorem w_ok : allN 336 (fun i => wordR (wdec (WT i)) == (q0Data.map rl).getD i R4.one) = true := by
  quickRfl

@[expose] def r4key (a : R4) : ℕ :=
  a.a00 + 4 * (a.a01 + 4 * (a.a02 + 4 * (a.a03 + 4 * (a.a10 + 4 * (a.a11 + 4 * (a.a12 +
    4 * (a.a13 + 4 * (a.a20 + 4 * (a.a21 + 4 * (a.a22 + 4 * (a.a23 + 4 * (a.a30 +
    4 * (a.a31 + 4 * (a.a32 + 4 * a.a33))))))))))))))

theorem q0_ok : (q0Data.map rl).length = 336 ∧ (q0Data.map rl).Nodup := by
  refine ⟨by rw [List.length_map]; rfl, List.Nodup.of_map r4key ?_⟩
  exact CFSG.KS.PCnt.nodup_of_distB (by quickRfl)

theorem shat_ok : (shatData.map rl).length = 16 ∧ (shatData.map rl).Nodup ∧
    R4.one ∈ shatData.map rl ∧
    (∀ a ∈ shatData.map rl, ∀ b ∈ shatData.map rl, rmul a b ∈ shatData.map rl) ∧
    (∀ a ∈ shatData.map rl, ∃ b ∈ shatData.map rl, rmul a b = R4.one ∧ rmul b a = R4.one) ∧
    (∃ a ∈ shatData.map rl, a.a22 = 3) := by
  decide +kernel

end CertificateChecks.KernelTwoHSLe4.S9

end
