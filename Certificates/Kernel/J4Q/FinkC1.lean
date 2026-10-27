module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkData
public import Certificates.Kernel.J4Q.C4016
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.ComponentClassification.RankTwoSporadic.J4Fink

@[expose] noncomputable def finkY7K : Nat :=
  wordJ c rm one ([A, B] ++ [L0, L1, L2]) ([Ai, Bi] ++ [L0i, L1i, L2i]) y7Word

@[expose] noncomputable def pK : Nat :=
  mulJ c rm (etaK c rm one Us 911)
    (mulJ c rm (mulJ c rm finkY7K (etaK c rm one Us 911)) (powJ c rm one finkY7K 6))

theorem e0V_wf : e0V.wf = true := by decide

theorem kC1 : (Nat.beq (powJ c rm one pK 4) one &&
    neN (vecJ rm (v2N e0V) (powJ c rm one pK 2)) (v2N e0V)) = true := by quickRfl

theorem finkC1 : chkFinkC1 = true := by
  obtain ⟨hyw, hye⟩ := enc_wordRows hK mix_gens mix_invs y7Word
  obtain ⟨huw, hue⟩ := eta_enc 911
  unfold chkFinkC1 mixRowsOf z2Mask
  simp only []
  have hp := wf_mulRows huw (wf_mulRows (wf_mulRows hyw huw) (wf_powRows hyw 6))
  rw [eqRows_eq (wf_powRows hp 4) wf_idRows, differs_eq (wf_frApply (wf_powRows hp 2) _) e0V_wf,
    v2N_frApply hK (wf_powRows hp 2) e0V_wf, enc_powRows hK hp, enc_powRows hK hp,
    enc_mulRows hK huw (wf_mulRows (wf_mulRows hyw huw) (wf_powRows hyw 6)),
    enc_mulRows hK (wf_mulRows hyw huw) (wf_powRows hyw 6), enc_mulRows hK hyw huw,
    enc_powRows hK hyw, enc_idRows hK, hye, hue]
  exact kC1

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem c15039 : chkFinkC1 = true := finkC1

end CertificateChecks.KernelJ4Q

end
