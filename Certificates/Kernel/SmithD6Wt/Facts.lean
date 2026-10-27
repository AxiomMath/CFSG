module

public import Certificates.Kernel.SmithD6Wt.Checks
import Certificates.Kernel.SmithD6Wt.Close0
import Certificates.Kernel.SmithD6Wt.Close1
import Certificates.Kernel.SmithD6Wt.Close2
import Certificates.Kernel.SmithD6Wt.Close3
public import Certificates.Kernel.SmithD6Trees.Checks
public import CFSG.Certificates.Kernel.SmithD6WtSound
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Wt

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

#kc_forall_chunks closeChunks_ok (fun i => d6CloseOK (i / 13) (i % 13) = true) 481
  CertificateChecks.SmithD6Wt.d6cl 1

theorem wt64_facts :
    J.wt64C.flatten.Pairwise (· < ·) ∧ J.wt64C.flatten.length = 75735 ∧
    (∀ i (hi : i < J.wt64C.flatten.length), wt64Tree.find J.wt64C.flatten[i] = i + 1) ∧
    ∀ x v, wt64Tree.find x = v + 1 →
      ∃ hv : v < J.wt64C.flatten.length, J.wt64C.flatten[v] = x := by
  have hl : J.wt64C.length = 37 := by rw [← lenC_eq, wt64C_lenC]
  exact KT.chunks_sound (List.ne_nil_of_length_pos (by rw [hl]; decide)) (by decide)
    (fun c hc => wt64Chunks_ok c (by rw [hl] at hc; exact hc)) wt64Tree_size

theorem wt64_eq_map :
    J.wt64C.flatten = J.wtC.flatten.map exC ∧ ∀ x ∈ J.wtC.flatten, x < 4294967296 := by
  have h64 : J.wt64C.length = 37 := by rw [← lenC_eq, wt64C_lenC]
  have h32 : J.wtC.length = 37 := by rw [← lenC_eq, SmithD6Trees.wtC_lenC]
  have hc : ∀ c < 37, J.wt64C.getD c [] = (J.wtC.getD c []).map exC ∧
      ∀ x ∈ J.wtC.getD c [], x < 4294967296 := fun c hc => by
    have h := exChunks_ok c hc
    rw [d6ExOK, nthC_eq, nthC_eq] at h
    exact exPinGo_sound _ _ h
  have heq : J.wt64C = J.wtC.map (List.map exC) := by
    apply List.ext_getElem (by simp [h64, h32])
    intro c h1 h2
    have := (hc c (by omega)).1
    rw [getD_eq h1, getD_eq (by omega)] at this
    simp [this]
  refine ⟨by rw [heq, ← List.map_flatten], fun x hx => ?_⟩
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 hx
  obtain ⟨c, hc', rfl⟩ := List.getElem_of_mem hl
  exact (hc c (by omega)).2 x (by rw [getD_eq hc']; exact hx)

theorem closure : ∀ s ∈ J.wt64C.flatten, ∀ g < 13,
    wt64Tree.memB (liftT (JT.gensT.getD g []) s) = true := by
  have h64 : J.wt64C.length = 37 := by rw [← lenC_eq, wt64C_lenC]
  intro s hs g hg
  obtain ⟨l, hl, hs⟩ := List.mem_flatten.1 hs
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hl
  rw [h64] at hc
  have hb : 13 * c + g < 481 := by omega
  have h := closeChunks_ok (13 * c + g) hb
  rw [show (13 * c + g) / 13 = c by omega, show (13 * c + g) % 13 = g by omega, d6CloseOK,
    nthC_eq, getD_eq (l := J.wt64C) (i := c) (by rw [h64]; exact hc)] at h
  exact closeGo_sound _ h s hs

theorem planes : ∀ c < 37, (J.pbC.getD c []).length = (J.wt64C.getD c []).length ∧
    (J.ppC.getD c []).length = (J.wt64C.getD c []).length ∧
    ∀ i < (J.wt64C.getD c []).length, planeL ((J.wt64C.getD c []).getD i 0)
      ((J.pbC.getD c []).getD i #[]).toList ((J.ppC.getD c []).getD i #[]).toList = true := by
  intro c hc
  have h := planeChunks_ok c hc
  rw [d6PlaneOK, nthC_eq, nthA_eq, nthA_eq] at h
  exact planeGo_sound _ _ _ h

end CertificateChecks.SmithD6Wt

end
