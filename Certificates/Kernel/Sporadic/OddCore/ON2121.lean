module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.DecSLSound
public import CFSG.Sporadic.ONOddCore.LiftCountInputs
meta import CFSG.Sporadic.ONOddCore.LiftCountInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.LiftsT CFSG.Sporadic.ONOddCore.liftsText

namespace CertificateChecks.KernelSpor.ON2121

open CFSG.Sporadic.ONOddCore CFSG.KS.DecSL

@[expose] def liftE : List (List Nat) :=
  [[0, 3, 1, 2], [], [], [0, 3, 2, 1], [], [], [], [], [], [0, 2, 3, 1], [0, 3, 1, 2], []]

theorem digits : digitsSLOK LiftsT.chars = true := by
  quickRfl

theorem cands_eq : (decodeLifts (natsSL LiftsT.chars)).cands.map liftIdxs = liftE := by
  kernelRfl

theorem liftIdxs_eq (k : Nat) : liftIdxs (liftData.cands.getD k []) = liftE.getD k [] := by
  have h : liftData = decodeLifts (natsSL LiftsT.chars) := by
    rw [liftData, LiftsT.eq, natsOf_ofList digits]
  rw [← cands_eq, ← h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases liftData.cands[k]? <;> rfl

theorem facts2121 : (List.range 12).map (fun k => (liftIdxs (liftData.cands.getD k [])).length) =
      [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0] ∧
    (List.range 12).all (fun k => (liftIdxs (liftData.cands.getD k [])).Nodup) = true := by
  simp only [liftIdxs_eq]
  decide

end CertificateChecks.KernelSpor.ON2121

end
