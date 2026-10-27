module

public import Certificates.Kernel.SmithD6Wt.Tree
public import CFSG.Certificates.Kernel.SmithD6WtTreeSound
public import CFSG.GF2Type.SmithTypeE.DMod.GensV

set_option maxRecDepth 100000

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.SmithD6Wt

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem tree_recs : ∀ i < 75735, wtRecOK JG.wtD JG.wtG (J.wt64C.flatten.getD i 0) i = true := by
  intro i hi
  have hl : J.wt64C.length = 37 := wt64C_length
  have hc : i / 2048 < J.wt64C.length := by rw [hl]; omega
  have hc37 : i / 2048 < 37 := by rw [hl] at hc; exact hc
  obtain ⟨hf, hlen, -⟩ := chunkOK_sound hc (wt64Chunks_ok (i / 2048) hc37)
  have hj : i % 2048 < J.wt64C[i / 2048].length := by
    rw [hl] at hlen
    split_ifs at hlen with h <;> omega
  have h := wtTreeChunks_ok (i / 2048) hc37
  rw [d6WtTreeOK, nthC_eq] at h
  have h2 := wtTreeGo_sound _ _ h (i % 2048) (by rw [getD_eq hc]; exact hj)
  have hfi := hf (i % 2048) hj
  have hi' : 2048 * (i / 2048) + i % 2048 = i := Nat.div_add_mod i 2048
  rw [hi'] at hfi
  obtain ⟨hv, hx⟩ := wt64_facts.2.2.2 _ _ hfi
  have key : J.wt64C.flatten.getD i 0 = (J.wt64C.getD (i / 2048) []).getD (i % 2048) 0 := by
    rw [List.getD_eq_getElem _ _ hv, hx, getD_eq hc]
    exact (List.getD_eq_getElem _ _ hj).symm
  rw [Nat.mul_eq, hi'] at h2
  rw [key]
  exact h2

theorem tree_codes (Q : ℕ → Prop) (h0 : Q 0)
    (hstep : ∀ g < 13, ∀ i < 75735, ∀ p < 75735,
      liftT (JT.gensT.getD g []) (J.wt64C.flatten.getD i 0) = J.wt64C.flatten.getD p 0 →
        Q p → Q i) :
    ∀ i < 75735, Q i := by
  refine wtTree_induct tree_recs (fun x v hv => ?_) Q h0 hstep
  obtain ⟨hvl, hx⟩ := wt64_facts.2.2.2 x v hv
  refine ⟨by rw [wt64_facts.2.1] at hvl; exact hvl, ?_⟩
  rw [List.getD_eq_getElem _ _ hvl, hx]

theorem tree32 (Q : ℕ → Prop) (h0 : Q 0)
    (hstep : ∀ g < 13, ∀ p < 75735, ∀ i < 75735,
      tlift (dec12 (gensV.getD g (0, 0)).1) (dec12 (gensV.getD g (0, 0)).2)
          (exL (decode32 (J.wtC.flatten.getD p 0))) = exL (decode32 (J.wtC.flatten.getD i 0)) →
        Q p → Q i) :
    ∀ i < 75735, Q i := by
  refine tree_codes Q h0 fun g hg i hi p hp he hQ => hstep g hg p hp i hi ?_ hQ
  obtain ⟨-, -, -, -, h1, h2, -, h3⟩ := gensV_codes g hg
  have hts := tsPair_dec12 h1 h2 h3
  have e := congrArg decode64 he
  rw [wt64_getD, wt64_getD, decode64_liftT (gensT_ok g hg) (exC_lt_two_pow _), decode64_exC,
    decode64_exC] at e
  rw [← e, tlift_apply_tlift hts]

end CertificateChecks.SmithD6Wt

end
