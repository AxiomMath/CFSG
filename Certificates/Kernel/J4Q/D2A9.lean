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

theorem a941Words_eq : a941Words = d2A9W := by
  rw [A9W.eq]
  simp only [← String.ofList_append, w5_ofList, d2A9W, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem a941q_eq : a941q = d2A9Q := by
  rw [A9Q.eq]
  simp only [← String.ofList_append, w5_ofList, d2A9Q, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem a9g_chk : andB (allR 4 fun k => Nat.beq (getN one A9G k) (wordJ c rm one G5 G5i (d2A9W.getD k [])))
    (Nat.beq A9Q (wordJ c rm one G5 G5i d2A9Q)) = true := by quickRfl

theorem a9_hG : ∀ k < 4, WfA (wR (a941Words.getD k [])) ∧ encR (wR (a941Words.getD k [])) = getN one A9G k := by
  intro k hk
  have h := a9g_chk
  rw [andB_eq, Bool.and_eq_true] at h
  rw [a941Words_eq]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true (allR_spec h.1 k hk)).symm⟩

theorem a9_hQ : WfA (wR a941q) ∧ encR (wR a941q) = A9Q := by
  have h := a9g_chk
  rw [andB_eq, Bool.and_eq_true] at h
  rw [a941q_eq]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true h.2).symm⟩

theorem a9_grp : d2GrpK A9G = true := by quickRfl

theorem a9_norm : d2NormK A9G = true := by quickRfl

@[expose] noncomputable def a9K0 (c : Nat) : Bool := d2K0K A9G c

#j4q_all CFSG.KD.J4Q.A9K CertificateChecks.KernelJ4Q.a9K0 105

theorem a9_n : d2NK A9G 0 1 4 = true := by quickRfl

theorem a9_w : d2WK A9G A9Q A9QI = true := by quickRfl

theorem a9_all : CFSG.QuasithinUnique.A5.Dec2.chkAll a941Words (wR a941q) = true :=
  chkAll_of a941Words A9G a9_hG (by rw [a941Words_eq]; rfl) a9_hQ a9_grp a9_norm A9K.all a9_n a9_w

end CertificateChecks.KernelJ4Q

end
