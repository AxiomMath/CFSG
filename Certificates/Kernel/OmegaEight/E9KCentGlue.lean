module

public import Certificates.Kernel.OmegaEight.E9KCent
public import Certificates.Kernel.OmegaEight.E9KGlue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO8pCentCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E9K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.PGrp
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.PartTwo.Sec4.Item434O8pE9 CFSG.AGLEmbedding.O8pCent
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord)
open CertificateChecks.KernelO8

theorem centCheck_true : centCheck o8pE9 [1] 9 = true := by
  have hl : ∀ l ∈ [1], l < 3 := by decide
  obtain ⟨eg, pg⟩ := posWord_unpack hw9 (fun l hl => (qgen hl).1) (fun l hl => (qgen hl).2) hl
  have hc := cent
  unfold centK at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hD, hb⟩ := hc
  unfold centCheck centCheck'
  rw [n_eq, eg, qsize]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hany
    obtain ⟨x, hx, hex⟩ := List.any_eq_true.1 hany
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    rw [Array.length_toList, d_size] at hi
    have e : (dCert o8pE9).pts.toList[i]'(by rw [Array.length_toList, d_size]; exact hi) =
        unpack 360 9 (E9D.T i) := by
      rw [Array.getElem_toList, ← getElem!_pos (dCert o8pE9).pts i (by rw [d_size]; exact hi),
        d_get i hi]
    rw [← hxi, e, eqA_unpack' hw9 pg (permD hi)] at hex
    have h1 := allN_spec hD i hi
    rw [hex] at h1
    exact absurd h1 (by decide)
  · have hcount : commCount 360 (dCert o8pE9) (unpack 360 9 (posWordK 360 9 E9Q.G [1])) =
        commK (posWordK 360 9 E9Q.G [1]) := by
      unfold commCount commK
      rw [d_size]
      congr 1
      apply List.filter_congr
      intro i hi
      have hi' := List.mem_range.1 hi
      rw [d_get i hi', comp_unpack' hw9 pg (permD hi'), comp_unpack' hw9 (permD hi') pg,
        eqA_unpack' hw9 (permB_pcomp hw9 pg (permD hi')) (permB_pcomp hw9 (permD hi') pg)]
      rfl
    rw [hcount]
    exact Nat.le_of_ble_eq_true hb

end CertificateChecks.KernelO8.E9K

end
