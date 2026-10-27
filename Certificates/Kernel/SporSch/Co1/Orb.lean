module

public import CFSG.Certificates.Kernel.SporSch.Co1OrbSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Orb

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree CFSG.KS.SporSch.Orb

theorem k : orbK Data.orbTree0 Data.orbTree1 Data.orbTree2 Data.orbTree3 Data.conjExps
    Data.eigenchars = true := by quickRfl

theorem facts : (∀ k, treeOK k = true ∧ treeClosed k = true ∧
      ∀ c ∈ treeCodes k, encodeF (decodeF c) = c) ∧
    (∀ f, ∃ k, encodeF f ∈ treeCodes k) ∧ (∀ f, decodeF (encodeF f) = f) ∧
    (∀ f, encodeF f ∈ treeCodes 1 ↔ ∃ j, f = γ j ∨ f = -γ j) :=
  have h := orbK_sound k
  ⟨h.1, h.2.1, decodeF_encodeF, h.2.2⟩

end CertificateChecks.KernelSporSch.Co1Orb

end
