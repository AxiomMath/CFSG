module

public import Certificates.Kernel.SmithD6Trees.Checks
public import CFSG.Certificates.Kernel.KeyTreeChunksSound

public section

namespace CertificateChecks.SmithD6Trees

open CFSG.KC.KeyTree CFSG.KD.SmithD6

theorem lineKeys_facts :
    J.lineKeysC.flatten.Pairwise (· < ·) ∧ J.lineKeysC.flatten.length = 365211 ∧
    (∀ i (hi : i < J.lineKeysC.flatten.length), lineTree.find J.lineKeysC.flatten[i] = i + 1) ∧
    ∀ x v, lineTree.find x = v + 1 →
      ∃ hv : v < J.lineKeysC.flatten.length, J.lineKeysC.flatten[v] = x := by
  have hl : J.lineKeysC.length = 179 := by rw [← lenC_eq, lineKeysC_lenC]
  exact KT.chunks_sound (List.ne_nil_of_length_pos (by rw [hl]; decide)) (by decide)
    (fun c hc => lineChunks_ok c (by rw [hl] at hc; exact hc)) lineTree_size

theorem wt_facts :
    J.wtC.flatten.Pairwise (· < ·) ∧ J.wtC.flatten.length = 75735 ∧
    (∀ i (hi : i < J.wtC.flatten.length), wtTree.find J.wtC.flatten[i] = i + 1) ∧
    ∀ x v, wtTree.find x = v + 1 → ∃ hv : v < J.wtC.flatten.length, J.wtC.flatten[v] = x := by
  have hl : J.wtC.length = 37 := by rw [← lenC_eq, wtC_lenC]
  exact KT.chunks_sound (List.ne_nil_of_length_pos (by rw [hl]; decide)) (by decide)
    (fun c hc => wtChunks_ok c (by rw [hl] at hc; exact hc)) wtTree_size

end CertificateChecks.SmithD6Trees

end
