
module

public import Certificates.Kernel.J4Q.Dec2K
public import Certificates.Kernel.J4Q.Dec2Words
public import Certificates.Kernel.J4Q.Dec2Data
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.QuasithinUnique.A5

theorem a85Words_eq : a85Words = d2A8W := by
  rw [A8W.eq]
  simp only [← String.ofList_append, w5_ofList, d2A8W, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem a85q_eq : a85q = d2A8Q := by
  rw [A8Q.eq]
  simp only [← String.ofList_append, w5_ofList, d2A8Q, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem a8g_chk : andB (allR 4 fun k => Nat.beq (getN one A8G k) (wordJ c rm one G5 G5i (d2A8W.getD k [])))
    (Nat.beq A8Q (wordJ c rm one G5 G5i d2A8Q)) = true := by quickRfl

theorem a8_hG : ∀ k < 4, WfA (wR (a85Words.getD k [])) ∧ encR (wR (a85Words.getD k [])) = getN one A8G k := by
  intro k hk
  have h := a8g_chk
  rw [andB_eq, Bool.and_eq_true] at h
  rw [a85Words_eq]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true (allR_spec h.1 k hk)).symm⟩

theorem a8_hQ : WfA (wR a85q) ∧ encR (wR a85q) = A8Q := by
  have h := a8g_chk
  rw [andB_eq, Bool.and_eq_true] at h
  rw [a85q_eq]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true h.2).symm⟩

theorem a8_grp : d2GrpK A8G = true := by quickRfl

theorem a8_norm : d2NormK A8G = true := by quickRfl

@[expose] noncomputable def a8K0 (c : Nat) : Bool := d2K0K A8G c

#j4q_all CFSG.KD.J4Q.A8K CertificateChecks.KernelJ4Q.a8K0 105

theorem a8_n : d2NK A8G 0 1 4 = true := by quickRfl

theorem a8_w : d2WK A8G A8Q A8QI = true := by quickRfl

theorem a8_all : CFSG.QuasithinUnique.A5.Dec2.chkAll a85Words (wR a85q) = true :=
  chkAll_of a85Words A8G a8_hG (by rw [a85Words_eq]; rfl) a8_hQ a8_grp a8_norm A8K.all a8_n a8_w

end CertificateChecks.KernelJ4Q

end
