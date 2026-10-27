module

public import Certificates.Kernel.J4Q.Dec2K
public import Certificates.Kernel.J4Q.Dec2Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B336Data
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.QuasithinUnique.A5.Dec2

theorem b3g_chk : andB (allR 4 fun k => Nat.beq (getN one B3G k) (wordJ c rm one G5 G5i (wsB336.getD k [])))
    (Nat.beq B3Q (etaK c rm one Us 1)) = true := by quickRfl

theorem b3_hG : ∀ k < 4, WfA (wR (wsB336.getD k [])) ∧ encR (wR (wsB336.getD k [])) = getN one B3G k := by
  intro k hk
  have h := b3g_chk
  rw [andB_eq, Bool.and_eq_true] at h
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true (allR_spec h.1 k hk)).symm⟩

theorem b3_hQ : WfA (etaE 1) ∧ encR (etaE 1) = B3Q := by
  have h := b3g_chk
  rw [andB_eq, Bool.and_eq_true] at h
  have e := eta_enc 1
  exact ⟨e.1, e.2.trans (Nat.eq_of_beq_eq_true h.2).symm⟩

theorem b3_grp : d2GrpK B3G = true := by quickRfl

theorem b3_norm : d2NormK B3G = true := by quickRfl

@[expose] noncomputable def b3K0 (c : Nat) : Bool := d2K0K B3G c

#j4q_all CFSG.KD.J4Q.B3K CertificateChecks.KernelJ4Q.b3K0 105

theorem b3_n : d2NK B3G 0 1 4 = true := by quickRfl

theorem b3_w : d2WK B3G B3Q B3QI = true := by quickRfl

theorem b3_len : wsB336.length = 4 := by
  unfold wsB336
  simp

theorem b3_all : chkAll wsB336 (etaE 1) = true :=
  chkAll_of wsB336 B3G b3_hG b3_len b3_hQ b3_grp b3_norm B3K.all b3_n b3_w

end CertificateChecks.KernelJ4Q

end
