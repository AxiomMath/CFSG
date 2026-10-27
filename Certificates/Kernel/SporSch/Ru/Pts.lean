module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.SporSch.RuSound
public import CFSG.Sporadic.Schreier.RuDefs
meta import CFSG.Sporadic.Schreier.RuDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.RuPts CFSG.Sporadic.RuSchreier.ruPtsText

namespace CertificateChecks.KernelSporSch.RuPts

open CFSG.KS.SporSch CFSG.Sporadic.RuSchreier

theorem run : hexRunK 3 4060 10120 chars = true := by quickRfl

theorem offs : ∀ f < 9, (ruPtsOffsets.getD f (0, 0)).1 + (ruPtsOffsets.getD f (0, 0)).2 ≤ 10120 := by
  decide

theorem pts : ruBytesPts.size = 3 * 10120 ∧
    ∀ f < 9, ∀ i < (ruPtsOffsets.getD f (0, 0)).2, (ruPtList f)[i]! < 4060 := by
  have h := hexRunK_sound run
  rw [← eq] at h
  refine ⟨h.1, fun f hf i hi => ?_⟩
  rw [ruPtList, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact h.2 _ (by have := offs f hf; omega)

end CertificateChecks.KernelSporSch.RuPts

end
