module

public import CFSG.Monster.B.TwoA.Census.XiFusionInputs

public section

namespace CertificateChecks.KernelXiFusion

open CFSG.Monster.B.TwoA.Census

set_option maxHeartbeats 0

theorem arr_check0 :
    ∀ e ∈ xiEdges.take 1, mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) := by
  decide +kernel

theorem arr_check1 : ∀ e ∈ (xiEdges.drop 1).take 1,
    mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) := by
  decide +kernel

theorem arr_check2 :
    ∀ e ∈ xiEdges.drop 2, mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) := by
  decide +kernel

theorem arr_check :
    ∀ e ∈ xiEdges, mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) := by
  intro e he
  rw [← List.take_append_drop 1 xiEdges, List.mem_append] at he
  rcases he with he | he
  · exact arr_check0 e he
  rw [← List.take_append_drop 1 (xiEdges.drop 1), List.mem_append] at he
  rcases he with he | he
  · exact arr_check1 e he
  · exact arr_check2 e (by simpa [List.drop_drop] using he)

end CertificateChecks.KernelXiFusion

end
