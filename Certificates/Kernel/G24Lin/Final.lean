module

public import CFSG.Certificates.Kernel.G24LinQSound
public import Certificates.Kernel.G24Lin.Checks

public section

namespace CFSG.KD.G24Lin

open CFSG.Quasithin.St84.G24LE CFSG.Quasithin.St84.G24MF CFSG.KC.G24Lin
open CFSG.Quasithin.H.Q13 (om)

theorem andL {a b : Bool} (h : (a && b) = true) : a = true := by
  rw [Bool.and_eq_true] at h
  exact h.1

theorem andR {a b : Bool} (h : (a && b) = true) : b = true := by
  rw [Bool.and_eq_true] at h
  exact h.2

theorem lin733012_kR1 : ∀ x, (quadRows 8 2)[quadRowKey x]? = some x := by decide +kernel

theorem lin733012_kC1 : ∀ x, (quadCols 8 2)[quadColKey x]? = some x := by decide +kernel

theorem lin733012_kR2 : ∀ x, (quadRows 6 4)[quadRowKey x]? = some x := by decide +kernel

theorem lin733012_kC2 : ∀ x, (quadCols 6 4)[quadColKey x]? = some x := by decide +kernel

theorem lin733012_kRc : ∀ x, commRows[commRowKey x]? = some x := by decide +kernel

theorem lin733012_kCc : ∀ x, commCols[commColKey x]? = some x := by decide +kernel

theorem lin733012_kRe : ∀ x, ext2Rows[ext2RowKey x]? = some x := by decide +kernel

theorem lin733012_kCe : ∀ x, ext2Cols[ext2ColKey x]? = some x := by decide +kernel

theorem lin733012_kKe : ∀ x, ext2KList[ext2KKey x]? = some x := by decide +kernel

theorem lin733012_kF2 : ∀ x : Fin 2, (List.finRange 2)[x.val]? = some x := by decide +kernel

theorem lin733012_kM1 : ∀ x : Mono 8, (monoList 8)[monoKey x]? = some x := by decide +kernel

theorem lin733012_kM2 : ∀ x : Mono 6, (monoList 6)[monoKey x]? = some x := by decide +kernel

theorem lin733012_len : (quadRows 8 2).length = 216 ∧ (quadCols 8 2).length = 72 ∧
    (quadRows 6 4).length = 252 ∧ (quadCols 6 4).length = 84 ∧ commRows.length = 32 ∧
    commCols.length = 16 ∧ ext2Rows.length = 48 ∧ ext2Cols.length = 24 ∧ ext2KList.length = 10 ∧
    pq1.chars.length = 2 ∧ yq1.chars.length = 72 ∧ pq2.chars.length = 2 ∧ yq2.chars.length = 84 ∧
    pcm.chars.length = 2 ∧ ycm.chars.length = 16 ∧ pe2.chars.length = 10 ∧
    ye2.chars.length = 24 := by
  decide +kernel

theorem lin733012_card : Fintype.card (Fin 3 × Mono 8 × Fin 2) = (quadRows 8 2).length ∧
    Fintype.card (Mono 8 × Fin 2) = (quadCols 8 2).length ∧
    Fintype.card (Fin 3 × Mono 6 × Fin 4) = (quadRows 6 4).length ∧
    Fintype.card (Mono 6 × Fin 4) = (quadCols 6 4).length ∧
    Fintype.card (Fin 2 × Fin 4 × Fin 4) = commRows.length ∧
    Fintype.card (Fin 4 × Fin 4) = commCols.length ∧
    Fintype.card (Fin 6 × Fin 2 × Fin 4) = ext2Rows.length ∧
    Fintype.card (Fin 3 × Fin 2 × Fin 4) = ext2Cols.length ∧
    Fintype.card ((Fin 2 × Fin 4) ⊕ Fin 2) = ext2KList.length ∧
    Fintype.card (Fin 2) = (List.finRange 2).length := by
  decide +kernel

theorem mem_gjList {n : ℕ} (g : Fin 3) (j : Fin n) : (g, j) ∈ gjList n := by
  simp [gjList]

theorem lin733012_lanes1 :
    (∀ g i j, matV1 g i j = bz (laneK (CQ1 0) (g.val * 8 + j.val)) i.val) ∧
    (∀ g t s, matZ1 g t s = bz (laneK (CQ1 1) (g.val * 2 + t.val)) s.val) ∧
    (∀ (μ : Mono 8) (i : Fin 8), testVec μ i = bz (laneK (CQ1 2) (monoKey μ)) i.val) := by
  refine ⟨fun g i j => ?_, fun g t s => ?_, fun μ i => ?_⟩
  · have e := pinM_spec lin733012_r1 (g, j) (mem_gjList g j) i (List.mem_finRange i)
    rwa [Nat.zero_add] at e
  · have e := pinM_spec lin733012_s1 (g, t) (mem_gjList g t) s (List.mem_finRange s)
    rwa [Nat.zero_add] at e
  · have e := pinM_spec lin733012_t1 μ (mem_of_keys lin733012_kM1 μ) i (List.mem_finRange i)
    rwa [Nat.zero_add] at e

theorem lin733012_lanes2 :
    (∀ g i j, matV2 g i j = bz (laneK (CQ2 0) (g.val * 6 + j.val)) i.val) ∧
    (∀ g t s, matZ2 g t s = bz (laneK (CQ2 1) (g.val * 4 + t.val)) s.val) ∧
    (∀ (μ : Mono 6) (i : Fin 6), testVec μ i = bz (laneK (CQ2 2) (monoKey μ)) i.val) := by
  refine ⟨fun g i j => ?_, fun g t s => ?_, fun μ i => ?_⟩
  · have e := pinM_spec lin733012_r2 (g, j) (mem_gjList g j) i (List.mem_finRange i)
    rwa [Nat.zero_add] at e
  · have e := pinM_spec lin733012_s2 (g, t) (mem_gjList g t) s (List.mem_finRange s)
    rwa [Nat.zero_add] at e
  · have e := pinM_spec lin733012_t2 μ (mem_of_keys lin733012_kM2 μ) i (List.mem_finRange i)
    rwa [Nat.zero_add] at e

theorem quad1Check_ok : quad1Check () = true := by
  obtain ⟨hR, hS, hT⟩ := lin733012_lanes1
  obtain ⟨l1, l2, -, -, -, -, -, -, -, l10, l11, -⟩ := lin733012_len
  unfold quad1Check
  simp only [pq1.eq, yq1.eq]
  exact spanOK_glue (quadRows 8 2) (quadCols 8 2) (List.finRange 2) quadRowKey quadColKey
    (fun κ => κ.val) lin733012_kR1 lin733012_kC1 lin733012_kF2 lin733012_card.1
    lin733012_card.2.1 lin733012_card.2.2.2.2.2.2.2.2.2 (quadM matV1 matZ1) _
    (quadM_entry matV1 matZ1 (CQ1 0) (CQ1 1) (CQ1 2) hR hS hT) (quadK sqV1 cmV1 om) pq1.chars
    yq1.chars DQ1 (by rw [l10, List.length_finRange]) (by rw [l11, l2])
    (by rw [List.length_finRange, l2]; exact lin733012_m1)
    (by rw [List.length_finRange]; exact lin733012_k1)
    (andL lin733012_p1)
    (by rw [List.length_finRange, l2]; exact (andR lin733012_p1))
    (by rw [List.length_finRange, l1, l2]; exact lin733012_q1)

theorem quad2Check_ok : quad2Check () = true := by
  obtain ⟨hR, hS, hT⟩ := lin733012_lanes2
  obtain ⟨-, -, l3, l4, -, -, -, -, -, -, -, l12, l13, -⟩ := lin733012_len
  unfold quad2Check
  simp only [pq2.eq, yq2.eq]
  exact spanOK_glue (quadRows 6 4) (quadCols 6 4) (List.finRange 2) quadRowKey quadColKey
    (fun κ => κ.val) lin733012_kR2 lin733012_kC2 lin733012_kF2 lin733012_card.2.2.1
    lin733012_card.2.2.2.1 lin733012_card.2.2.2.2.2.2.2.2.2 (quadM matV2 matZ2) _
    (quadM_entry matV2 matZ2 (CQ2 0) (CQ2 1) (CQ2 2) hR hS hT) (quadK sqV2 cmV2 omegaN)
    pq2.chars yq2.chars DQ2 (by rw [l12, List.length_finRange]) (by rw [l13, l4])
    (by rw [List.length_finRange, l4]; exact lin733012_m2)
    (by rw [List.length_finRange]; exact lin733012_k2)
    (andL lin733012_p2)
    (by rw [List.length_finRange, l4]; exact (andR lin733012_p2))
    (by rw [List.length_finRange, l3, l4]; exact lin733012_q2)

theorem commCheck_ok : commCheck () = true := by
  obtain ⟨-, -, -, -, l5, l6, -, -, -, -, -, -, -, l14, l15, -⟩ := lin733012_len
  unfold commCheck
  simp only [pcm.eq, ycm.eq]
  exact spanOK_glue commRows commCols (List.finRange 2) commRowKey commColKey (fun κ => κ.val)
    lin733012_kRc lin733012_kCc lin733012_kF2 lin733012_card.2.2.2.2.1
    lin733012_card.2.2.2.2.2.1 lin733012_card.2.2.2.2.2.2.2.2.2 commM commM (fun _ _ => rfl)
    commK pcm.chars ycm.chars DC (by rw [l14, List.length_finRange]) (by rw [l15, l6])
    (by rw [List.length_finRange, l6]; exact lin733012_mc)
    (by rw [List.length_finRange]; exact lin733012_kc)
    (andL lin733012_pc)
    (by rw [List.length_finRange, l6]; exact (andR lin733012_pc))
    (by rw [List.length_finRange, l5, l6]; exact lin733012_c)

theorem ext2Check_ok : ext2Check () = true := by
  obtain ⟨-, -, -, -, -, -, l7, l8, l9, -, -, -, -, -, -, l16, l17⟩ := lin733012_len
  unfold ext2Check
  simp only [pe2.eq, ye2.eq]
  exact spanOK_glue ext2Rows ext2Cols ext2KList ext2RowKey ext2ColKey ext2KKey
    lin733012_kRe lin733012_kCe lin733012_kKe lin733012_card.2.2.2.2.2.2.1
    lin733012_card.2.2.2.2.2.2.2.1 lin733012_card.2.2.2.2.2.2.2.2.1 ext2M ext2M (fun _ _ => rfl)
    ext2K pe2.chars ye2.chars DE (by rw [l16, l9]) (by rw [l17, l8])
    (by rw [l9, l8]; exact lin733012_me)
    (by rw [l9]; exact lin733012_ke)
    (andL lin733012_pe)
    (by rw [l9, l8]; exact (andR lin733012_pe))
    (by rw [l9, l8, l7]; exact lin733012_e)

theorem linEqCheck_ok : linEqCheck () = true := by
  unfold linEqCheck
  rw [quad1Check_ok, quad2Check_ok, commCheck_ok, ext2Check_ok]
  rfl

end CFSG.KD.G24Lin

end
