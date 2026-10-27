module

public import Certificates.Kernel.SmithD6Uw.Model
import all Certificates.Data.SmithD6Model

public section

namespace CertificateChecks.SmithD6Pinned

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KC.SmithD6Search

@[expose] def PinnedModel : Prop :=
  lineKeys = ⟨J.lineKeysC.flatten⟩ ∧ wtArr = ⟨J.wtC.flatten⟩ ∧ pbArr = ⟨J.pbC.flatten⟩ ∧
    ppArr = ⟨J.ppC.flatten⟩ ∧
    ∀ u w, lineIdx u w =
      if lowerBoundGo lineKeys (4096 * u + w) 40 0 lineKeys.size < 365211 &&
          lineKeys[lowerBoundGo lineKeys (4096 * u + w) 40 0 lineKeys.size]! == 4096 * u + w then
        lowerBoundGo lineKeys (4096 * u + w) 40 0 lineKeys.size
      else 365211

theorem mk_getElem! {α : Type} [Inhabited α] (l : List α) (i : ℕ) :
    (Array.mk l)[i]! = l.getD i default := by
  rw [← Array.getElem!_toList, List.getD_eq_getElem?_getD]
  by_cases h : i < l.length
  · simp [h]
  · simp [h]

namespace PinnedModel

variable (hM : PinnedModel)
include hM

theorem lineKeys_toList : lineKeys.toList = J.lineKeysC.flatten := by rw [hM.1]

theorem wtArr_toList : wtArr.toList = J.wtC.flatten := by rw [hM.2.1]

theorem pbArr_get : ∀ i < 75735, pbArr[i]! = J.pbC.flatten.getD i #[] := fun i _ => by
  rw [hM.2.2.1, mk_getElem!]
  rfl

theorem ppArr_get : ∀ i < 75735, ppArr[i]! = J.ppC.flatten.getD i #[] := fun i _ => by
  rw [hM.2.2.2.1, mk_getElem!]
  rfl

theorem wt_get : ∀ j (hj : j < J.wtC.flatten.length), wt j = J.wtC.flatten[j] :=
  fun _ hj => SmithD6Uw.wt_eq hM.wtArr_toList hj

theorem wtIdx_lt_iff_memB : ∀ x, wtIdx x < 75735 ↔ wtTree.memB x = true := fun x => by
  obtain ⟨-, -, hf, hs⟩ := SmithD6Trees.wt_facts
  rw [SmithD6Uw.wtIdx_lt_iff hM.wtArr_toList, SmithD6Uw.memB_iff_mem hf hs]

theorem lineIdx_eq_idx (u w : ℕ) : lineIdx u w = KT.idx 365211 (4096 * u + w) lineTree := by
  obtain ⟨hp, hn, hf, hs⟩ := SmithD6Trees.lineKeys_facts
  rw [hM.2.2.2.2 u w]
  exact search_eq_idx hM.lineKeys_toList hn (by norm_num) hp hf hs _

theorem lineKeys_lineIdx : ∀ u w, lineIdx u w < 365211 → lineKeys[lineIdx u w]! = 4096 * u + w := by
  intro u w h
  rw [hM.2.2.2.2 u w] at h ⊢
  generalize lowerBoundGo lineKeys (4096 * u + w) 40 0 lineKeys.size = i at h ⊢
  by_cases hc : i < 365211 ∧ lineKeys[i]! = 4096 * u + w
  · simp [hc.1, hc.2]
  · have hc' : ¬((decide (i < 365211) && lineKeys[i]! == 4096 * u + w) = true) := by
      simpa using hc
    rw [if_neg hc'] at h
    exact absurd h (lt_irrefl _)

theorem lineIdx_of_memB : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w) := by
  intro u w _ hw hm
  obtain ⟨-, hn, hf, hs⟩ := SmithD6Trees.lineKeys_facts
  obtain ⟨i, hi, hik⟩ := List.getElem_of_mem ((SmithD6Uw.memB_iff_mem hf hs _).1 hm)
  have hlt : lineIdx u w < 365211 := by
    rw [hM.lineIdx_eq_idx, (KT.idx_eq (N := 365211) hf hs _).1 i hi hik]
    omega
  refine ⟨hlt, ?_⟩
  have hk := hM.lineKeys_lineIdx u w hlt
  unfold linePair
  rw [hk]
  ext <;> dsimp only <;> omega

end PinnedModel

theorem gensArr_eq : gensArr = (gensV.map fun p => lineOf p.1 p.2).toArray := by
  apply Array.toList_inj.1
  simp only [gensArr, gensV, eV, fV, Array.toList_append, List.toList_toArray, List.map_cons,
    List.map_nil, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.append_nil, List.singleton_append]

theorem gensArr_get : ∀ g < 13,
    gensArr[g]! = lineOf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2 := by
  intro g hg
  rw [gensArr_eq, mk_getElem!, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  have hl : g < gensV.length := hg
  simp [List.getElem?_eq_getElem hl]

end CertificateChecks.SmithD6Pinned

end
