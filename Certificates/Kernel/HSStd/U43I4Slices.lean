module

public import Certificates.Kernel.HSStd.U43I4K
public import CFSG.Certificates.Kernel.U43WitSound

public section

namespace CertificateChecks.KernelHSStd.U43I4

open CFSG.KC.U43Case CFSG.KC.U43Wit CertificateChecks.KernelCU43Aut

theorem ns_all : ∀ i < 648,
    cFailK 820 10 (CU43T 6) (I4G 1) (I4Y i) (I4WC i) I4WK 648 I4Y = true := by
  intro i hi
  rcases (by omega : i < 81 ∨ (81 ≤ i ∧ i < 162) ∨ (162 ≤ i ∧ i < 243) ∨ (243 ≤ i ∧ i < 324) ∨
      (324 ≤ i ∧ i < 405) ∨ (405 ≤ i ∧ i < 486) ∨ (486 ≤ i ∧ i < 567) ∨ 567 ≤ i) with
    h | h | h | h | h | h | h | h
  · exact noSolK_at kNs0 (by omega) (by omega) hi
  · exact noSolK_at kNs1 h.1 (by omega) hi
  · exact noSolK_at kNs2 h.1 (by omega) hi
  · exact noSolK_at kNs3 h.1 (by omega) hi
  · exact noSolK_at kNs4 h.1 (by omega) hi
  · exact noSolK_at kNs5 h.1 (by omega) hi
  · exact noSolK_at kNs6 h.1 (by omega) hi
  · exact noSolK_at kNs7 h (by omega) hi

theorem tree_all : ∀ i, 0 < i → i < 648 →
    I4YP i < i ∧ I4YL i < 4 ∧ I4Y i = pp 820 10 (I4YG (I4YL i)) (I4Y (I4YP i)) := by
  intro i h0 hi
  rcases (by omega : i < 81 ∨ (81 ≤ i ∧ i < 162) ∨ (162 ≤ i ∧ i < 243) ∨ (243 ≤ i ∧ i < 324) ∨
      (324 ≤ i ∧ i < 405) ∨ (405 ≤ i ∧ i < 486) ∨ (486 ≤ i ∧ i < 567) ∨ 567 ≤ i) with
    h | h | h | h | h | h | h | h
  · exact treeK_at kTr0 (by omega) (by omega) hi h0
  · exact treeK_at kTr1 h.1 (by omega) hi h0
  · exact treeK_at kTr2 h.1 (by omega) hi h0
  · exact treeK_at kTr3 h.1 (by omega) hi h0
  · exact treeK_at kTr4 h.1 (by omega) hi h0
  · exact treeK_at kTr5 h.1 (by omega) hi h0
  · exact treeK_at kTr6 h.1 (by omega) hi h0
  · exact treeK_at kTr7 h (by omega) hi h0

end CertificateChecks.KernelHSStd.U43I4

end
