module

public import Certificates.Kernel.SmithD6Pinned.Model
import all Certificates.Data.SmithD6Model

public section

namespace CertificateChecks.SmithD6Pinned

open CFSG.SmithD6

theorem pinnedModel : PinnedModel := by
  unfold PinnedModel
  refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
  · unfold lineKeys
    rfl
  · unfold wtArr
    rfl
  · unfold pbArr
    rfl
  · unfold ppArr
    rfl

end CertificateChecks.SmithD6Pinned

end
