module

public import Certificates.Kernel.SmithD6Kc.MeetFacts
public import Certificates.Kernel.SmithD6Kc.Rank
public import CFSG.Certificates.Kernel.SmithD6RankSound

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Kc

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem arr_map_get! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {s : ℕ}
    (hs : s < a.size) : (a.map f)[s]! = f a[s]! := by
  rw [getElem!_pos (a.map f) s (by simpa using hs), Array.getElem_map, getElem!_pos a s hs]

theorem getA_eq_getD (a : Array (Array ℕ)) (k : ℕ) : a[k]! = a.toList.getD k #[] := by
  by_cases hk : k < a.size
  · rw [getElem!_pos a k hk, getD_eq (by simpa using hk)]
    simp
  · rw [getElem!_neg a k hk, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hk)]
    rfl

theorem lt_of_all {l : List ℕ} {s : ℕ} (h : l.all (· < 75735) = true) (hs : s < l.length) :
    l.getD s 0 < 75735 := by
  rw [getD_eq hs]
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.getElem_mem hs))

theorem rankOK_of (hpb : ∀ i < 75735, pbArr[i]! = J.pbC.flatten.getD i #[])
    (hpp : ∀ i < 75735, ppArr[i]! = J.ppC.flatten.getD i #[]) {R : ℕ} {rr cc inv : Array ℕ}
    (h1 : rr.toList.length = 33) (h2 : cc.toList.length = 33) (h3 : inv.toList.length = 33)
    (h4 : rr.toList.all (· < 75735) = true) (h5 : cc.toList.all (· < 75735) = true)
    (h6 : d6RankGo R cc.toList inv.toList rr.toList 0 = true) : rankOK R rr cc inv = true := by
  have s1 : rr.size = 33 := by rw [← Array.length_toList]; exact h1
  have s2 : cc.size = 33 := by rw [← Array.length_toList]; exact h2
  unfold rankOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨s1, s2⟩, by rw [← Array.length_toList]; exact h3⟩,
    by rw [← Array.all_toList]; exact h4⟩, by rw [← Array.all_toList]; exact h5⟩, ?_⟩
  rw [List.all_eq_true]
  intro s hs
  have hs' : s < 33 := List.mem_range.mp hs
  rw [List.all_eq_true]
  intro u _
  have hrow := d6RankGo_sound rr.toList 0 h6 s (by omega)
  rw [Nat.zero_add, d6RankRow_eq _ _ (by rw [h2, h3]), h2] at hrow
  have hb := congrArg (fun x => Nat.testBit x u) hrow
  unfold rankTerm at hb
  rw [testBit_foldl_xor] at hb
  have e : (List.range 33).foldl (fun acc t =>
      acc ^^ (((rr.map fun i => cc.map fun j => relD R i j)[s]!)[t]! && inv[t]!.testBit u)) false =
      (List.range 33).foldl (fun acc t =>
        acc ^^ (R.testBit (kcDist (d6MeetK (rr.toList.getD s 0) (cc.toList.getD t 0))) &&
          (inv.toList.getD t 0).testBit u)) false := by
    refine List.foldl_ext _ _ _ fun acc t ht => ?_
    have ht' : t < 33 := List.mem_range.mp ht
    rw [arr_map_get! _ rr (by omega), arr_map_get! _ cc (by omega), getElem!_eq_getD_toList,
      getElem!_eq_getD_toList, getElem!_eq_getD_toList, relD, distD,
      meetCnt_eq_d6MeetK hpb hpp (lt_of_all h4 (by omega)) (lt_of_all h5 (by omega)), kcDist_eq]
  rw [e, hb, Nat.testBit_two_pow]
  by_cases h : s = u <;> simp [h]

theorem chkRank_of_pinned (hpb : ∀ i < 75735, pbArr[i]! = J.pbC.flatten.getD i #[])
    (hpp : ∀ i < 75735, ppArr[i]! = J.ppC.flatten.getD i #[]) : chkRank = true := by
  have hpre : (rankRels == #[2, 4, 6, 10, 12, 14] && rankRows.size == 6 && rankCols.size == 6 &&
      rankInv.size == 6) = true := by decide +kernel
  have hsz : (List.range 6).all (fun r => (rankRows.toList.getD r #[]).toList.length == 33 &&
      (rankCols.toList.getD r #[]).toList.length == 33 &&
      (rankInv.toList.getD r #[]).toList.length == 33 &&
      (rankRows.toList.getD r #[]).toList.all (· < 75735) &&
      (rankCols.toList.getD r #[]).toList.all (· < 75735)) = true := by decide +kernel
  unfold chkRank
  rw [hpre, Bool.true_and, List.all_eq_true]
  intro r hr
  have hw := List.all_eq_true.mp hsz r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨w1, w2⟩, w3⟩, w4⟩, w5⟩ := hw
  have h6 := rank_ok r (List.mem_range.mp hr)
  unfold d6RankOK at h6
  rw [getElem!_eq_getD_toList, getA_eq_getD rankRows, getA_eq_getD rankCols,
    getA_eq_getD rankInv]
  exact rankOK_of hpb hpp w1 w2 w3 w4 w5 h6

end CertificateChecks.SmithD6Kc

end
