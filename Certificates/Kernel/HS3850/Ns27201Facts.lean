module

public import Certificates.Kernel.HS3850.Ns27201
public import Certificates.Kernel.TwoHS.HarGlue

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126
open CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS
open CFSG.KD.LQT.HO (Cn)

theorem ns_lt : ∀ r i : Fin 4, hnsBase r + i.val < 43 := by decide

theorem nsWordsA_ok : ∀ r : Fin 4, (hnsWordA r).all (fun l => decide (l.1.val < hnsNum r)) = true := by
  decide

theorem nsWordsB_ok : ∀ r : Fin 4, (hnsWordB r).all (fun l => decide (l.1.val < hnsNum r)) = true := by
  decide

theorem nsG_parts (r i : Fin 4) :
    hnsGen r i = tabT (unpack 3850 12 (nsG r i.val)) ∧ Cn (nsG r i.val) :=
  ⟨cent_tab (ns_lt r i), cent_cn (ns_lt r i)⟩

theorem ck27201_parts {r : Fin 4} (h : ck27201 r = true) :
    (∀ i < 4, canonK 3850 12 (mask 12) (3850 * 12) (nsGI r i) = true ∧
      invEqK 3850 12 (mask 12) (3850 * 12) (nsG r i) (nsGI r i) = true) ∧
    ordK (nsEV r (hnsWordA r)) 2 = true ∧ ordK (nsEV r (hnsWordB r)) 3 = true ∧
    ordK (pc (nsEV r (hnsWordA r)) (nsEV r (hnsWordB r))) 5 = true := by
  unfold ck27201 at h
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff, CFSG.KS.Raw.Orb.allN_iff] at h
  exact h

theorem nsGI_parts {r : Fin 4} (h : ck27201 r = true) (i : Fin 4) :
    hnsGenI r i = tabT (unpack 3850 12 (nsGI r i.val)) ∧ Cn (nsGI r i.val) := by
  obtain ⟨hc, he⟩ := (ck27201_parts h).1 i.val i.isLt
  refine ⟨?_, hc⟩
  unfold hnsGenI
  rw [(nsG_parts r i).1]
  exact invT_unpack (by norm_num) he

theorem nsEV_parts {r : Fin 4} (h : ck27201 r = true) (wd : List (Fin 4 × Bool)) :
    evalW 3850 (hnsGen r) (hnsGenI r) wd = tabT (unpack 3850 12 (nsEV r wd)) ∧
      Cn (nsEV r wd) := by
  have e : CFSG.KD.TwoHS.EV3 (fun i => nsG r i.val) (fun i => nsGI r i.val) wd = nsEV r wd := rfl
  rw [← e]
  exact CFSG.KD.TwoHS.evalW3_eq (nsG_parts r) (nsGI_parts h) wd

theorem hnsCheck_of {r : Fin 4} (h : ck27201 r = true) : hnsCheck r = true := by
  obtain ⟨hg, hA, hB, hAB⟩ := ck27201_parts h
  obtain ⟨eA, cA⟩ := nsEV_parts h (hnsWordA r)
  obtain ⟨eB, cB⟩ := nsEV_parts h (hnsWordB r)
  have p : (List.finRange 4).all (fun i =>
      permOK 3850 (hnsGen r i) && invOK 3850 (hnsGen r i) (hnsGenI r i)) = true := by
    rw [List.all_eq_true]
    intro i _
    obtain ⟨hc, he⟩ := hg i.val i.isLt
    rw [(nsGI_parts h i).1, (nsG_parts r i).1, permOK_unpack (nsG_parts r i).2 he,
      invOK_unpack (nsG_parts r i).2 hc he]
    rfl
  unfold hnsCheck
  rw [p, nsWordsA_ok r, nsWordsB_ok r]
  unfold hnsA hnsB
  rw [eA, eB, compT_pc cA cB, ord_of cA hA, ord_of cB hB, ord_of (cn_pc cA cB) hAB]
  rfl

theorem hnsOK_true : hnsOK = true := by
  unfold hnsOK
  rw [List.all_eq_true]
  intro r _
  apply hnsCheck_of
  fin_cases r
  · exact ok27201_0
  · exact ok27201_1
  · exact ok27201_2
  · exact ok27201_3

end CFSG.KD.HS3850

end
