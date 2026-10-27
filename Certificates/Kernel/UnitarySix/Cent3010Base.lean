
module

public import Certificates.Kernel.UnitarySix.KQFactsBase
public import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Certificates.NativeSchreierEnum
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Certificates CFSG.Certificates.Native
open CFSG.Certificates.ChainArrays CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

theorem kCent : centK (evList U.LT aWN) KQ.TR KQ.TRI (roff 693 (693 * 10) (KQ.LR 0))
    (roff 693 (693 * 10) (KQ.LR 1)) (roff 693 (693 * 10) (KQ.LR 2)) = true := by
  quickRfl

theorem kQ_lev_size :
    ∀ i < 3, (lev 693 KQ.SA kBase i).pts.size = [21, 16, 60].getD i 0 ∧
      rcnt (KQ.LR i) = [21, 16, 60].getD i 0 := by
  have hs := rawOrbitSizesK_sound KQ.binds KQ.perm KQ.hl
  have e : (List.range 3).map (fun i => rcnt (KQ.LR i)) = [21, 16, 60] := by decide
  rw [e] at hs
  have hl3 : (rawLevels 693 KQ.SA kBase).size = 3 := by simp [rawLevels, kBase]
  intro i hi
  refine ⟨?_, ?_⟩
  · rw [lev]
    exact KQ.size_of_orbitSizes hs (by rw [hl3]; exact hi)
  · interval_cases i <;> decide

end CertificateChecks.KernelU6

end
