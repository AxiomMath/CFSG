
module

public import Certificates.Kernel.J4Q.Dec2K
public import Certificates.Kernel.J4Q.Dec2Words
public import Certificates.Kernel.J4Q.Dec2Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B0Inputs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.QuasithinUnique.A5

theorem b1344Words_eq : b1344Words = d2B1W := by
  rw [B1W.eq]
  simp only [← String.ofList_append, w5_ofList, d2B1W, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem b1g_chk : andB (allR 4 fun k => Nat.beq (getN one B1G k) (wordJ c rm one G5 G5i (d2B1W.getD k [])))
    (Nat.beq B1Q (mulJ c rm (mulJ c rm (wordJ c rm one G5 G5i ((d2B1W.getD 0 []).take 25)) (etaK c rm one Us 269))
      (wordJ c rm one G5 G5i ((d2B1W.getD 0 []).drop 199)))) = true := by quickRfl

theorem b1_hG : ∀ k < 4, WfA (wR (b1344Words.getD k [])) ∧ encR (wR (b1344Words.getD k [])) = getN one B1G k := by
  intro k hk
  have h := b1g_chk
  rw [andB_eq, Bool.and_eq_true] at h
  rw [b1344Words_eq]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true (allR_spec h.1 k hk)).symm⟩

theorem b1_hQ : WfA b1344Q ∧ encR b1344Q = B1Q := by
  have h := b1g_chk
  rw [andB_eq, Bool.and_eq_true] at h
  have e := mul_enc hK (mul_enc hK (wR_enc b1344P) (eta_enc 269)) (wR_enc b1344S)
  unfold b1344P b1344S at e
  rw [b1344Words_eq] at e
  exact ⟨e.1, e.2.trans (Nat.eq_of_beq_eq_true h.2).symm⟩

theorem b1_grp : d2GrpK B1G = true := by quickRfl

theorem b1_norm : d2NormK B1G = true := by quickRfl

@[expose] noncomputable def b1K0 (c : Nat) : Bool := d2K0K B1G c

#j4q_all CFSG.KD.J4Q.B1K CertificateChecks.KernelJ4Q.b1K0 105

theorem b1_n : d2NK B1G 350 2 3 = true := by quickRfl

theorem b1_w : d2WK B1G B1Q B1QI = true := by quickRfl

theorem b1_all : CFSG.QuasithinUnique.A5.Dec2.chkAll b1344Words b1344Q = true :=
  chkAll_of b1344Words B1G b1_hG (by rw [b1344Words_eq]; rfl) b1_hQ b1_grp b1_norm B1K.all b1_n b1_w

end CertificateChecks.KernelJ4Q

end
