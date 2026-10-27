module

public import Certificates.Kernel.Sporadic.OddCore.ON2121
public import CFSG.Certificates.Kernel.Spor.DecSLProved

public section

namespace CertificateChecks.KernelSpor.ON2121

open CFSG.Sporadic.ONOddCore CFSG.KS.DecSL

theorem liftIdxs_eq_proved (k : Nat) : liftIdxs (liftData.cands.getD k []) = liftE.getD k [] := by
  have h : liftData = decodeLifts (natsSL LiftsT.chars) := by
    rw [liftData, LiftsT.eq, natsOf_ofList_proved digits]
  rw [← cands_eq, ← h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases liftData.cands[k]? <;> rfl

theorem facts2121_proved :
    (List.range 12).map (fun k => (liftIdxs (liftData.cands.getD k [])).length) =
      [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0] ∧
    (List.range 12).all (fun k => (liftIdxs (liftData.cands.getD k [])).Nodup) = true := by
  simp only [liftIdxs_eq_proved]
  decide

end CertificateChecks.KernelSpor.ON2121

end
