module

public import CFSG.Sporadic.J4.QTOutMatNative
public import Certificates.Kernel.J4Q.Mat
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem x0_eq : xRowsOf 1 = (locMats ())[0]?.getD (idRows ()) := by
  simp [xRowsOf, xRows]

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem c4022 : (eqRows (powRows (xRowsOf 1) 23) idRows = true)
    ∧ (wfRows (xRowsOf 1) = true)
    ∧ (eqRows (xRowsOf 1) idRows = false) := by
  obtain ⟨hw, he⟩ := loc_gens 0
  rw [← x0_eq] at hw he
  refine ⟨?_, wf_bool hw, ?_⟩
  · rw [eqRows_eq (wf_powRows hw 23) wf_idRows, enc_powRows hK hw, he, enc_idRows hK]
    quickRfl
  · rw [eqRows_eq hw wf_idRows, he, enc_idRows hK]
    refine beq_false (a := getN one [L0, L1, L2] 0) (b := one) ?_
    quickRfl

end CertificateChecks.KernelJ4Q

end
