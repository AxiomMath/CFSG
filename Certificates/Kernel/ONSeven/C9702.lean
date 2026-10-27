module

public import Certificates.Kernel.ONSeven.Lin
public import CFSG.RankThree.Native.ONThreeInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.ONLin CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ON.Native CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON (TT UU TT_lt x_get good_90 allBelowN_iff' peq_of)
open CertificateChecks.KernelSpor.ON3 (LetM)
open CertificateChecks.KernelSpor.ON8 (L onP sp agree lin_TT lin_UU)

theorem commChk : bAnd(onP (fun x => WW (onThreeY.getD 0 []) (TT 5 x))
      (fun x => TT 5 (WW (onThreeY.getD 0 []) x)),
    onP (fun x => WW (onThreeY.getD 1 []) (TT 5 x)) (fun x => TT 5 (WW (onThreeY.getD 1 []) x))) =
    true := by
  quickRfl

@[expose] noncomputable def tP (k : Nat) : Nat := onThreeTreePts.toList.getD k 0
@[expose] noncomputable def tQ (k : Nat) : Nat := onThreeTreePar.toList.getD k 0
@[expose] noncomputable def tG (k : Nat) : Nat := onThreeTreeGen.toList.getD k 0

theorem treeChk : allN 90 (fun k => Nat.blt (tP k) 245520 && Nat.beq (TT 5 (tP k)) (tP k) &&
    (allN k fun j => !(Nat.beq (tP j) (tP k))) &&
    (Nat.beq k 0 || (Nat.blt (tQ k) k && Nat.blt (tG k) 2 &&
      Nat.beq (WW (onThreeY.getD (tG k) []) (tP (tQ k))) (tP k)))) = true := by
  quickRfl

theorem letY {j : Nat} (hj : j < 2) : LetM 7 (onThreeY.getD j []) := by
  interval_cases j <;> (unfold LetM; decide)

theorem yArr_get {j p : Nat} (hj : j < 2) (hp : p < 245520) :
    (onThreeYArrs[j]!)[p]! = WW (onThreeY.getD j []) p := by
  have hs : onThreeY.size = 2 := rfl
  have e : onThreeYArrs[j]! = onSevenArr (onThreeY.getD j []) := by
    unfold onThreeYArrs
    rw [getElem!_pos _ j (by simp [hs]; omega), Array.getElem_map, getD_eq _ _ (by omega),
      getElem!_pos onThreeY j (by omega)]
  rw [e, arr_get (letY hj) hp]

theorem comm_check : onThreeCommOK (onSevenArr [6]) = true := by
  unfold onThreeCommOK
  refine allBelowN_iff'.2 fun j hj => ?_
  have hsz : onThreeYArrs.size = 2 := by simp [onThreeYArrs, onThreeY]
  have hj : j < 2 := hsz ▸ hj
  refine peq_of fun i hi => ?_
  have hi : i < 245520 := hi
  rw [pcomp_get hi, pcomp_get hi, x_get hi, yArr_get hj (TT_lt hi), yArr_get hj hi,
    x_get (WW_lt hi)]
  have h := commChk
  rw [bAnd_iff] at h
  have hc : onP (fun x => WW (onThreeY.getD j []) (TT 5 x))
      (fun x => TT 5 (WW (onThreeY.getD j []) x)) = true := by
    interval_cases j
    · exact h.1
    · exact h.2
  exact agree (Lin.comp (lin_WW (letY hj)) (lin_TT (by norm_num)))
    (Lin.comp (lin_TT (by norm_num)) (lin_WW (letY hj))) hc i hi

theorem tree_facts : ∀ k < 90, tP k < 245520 ∧ TT 5 (tP k) = tP k ∧ (∀ j < k, tP j ≠ tP k) ∧
    (k = 0 ∨ (tQ k < k ∧ tG k < 2 ∧ WW (onThreeY.getD (tG k) []) (tP (tQ k)) = tP k)) := by
  intro k hk
  have h := allN_spec treeChk k hk
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun j hj e => ?_, h4.imp id fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  have := allN_spec h3 j hj
  simp [e] at this

theorem tP_mem {k : Nat} (hk : k < 90) : tP k ∈ onThreeTreePts.toList := by
  unfold tP
  have hs : k < onThreeTreePts.toList.length := by
    have : onThreeTreePts.toList.length = 90 := rfl
    omega
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem hs

theorem tree_check :
    onThreeTreeOK onThreeYArrs onThreeTreePts onThreeTreePar onThreeTreeGen = true := by
  have hs : onThreeTreePts.size = 90 := rfl
  unfold onThreeTreeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨rfl, rfl⟩, rfl⟩, allBelowN_iff'.2 fun k hk => ?_⟩
  rw [hs] at hk
  obtain ⟨h1, -, -, h4⟩ := tree_facts k hk
  have eP : ∀ i < 90, onThreeTreePts[i]! = tP i := fun i hi => by
    unfold tP
    rw [getElem!_pos onThreeTreePts i (by rw [hs]; exact hi), ← Array.getElem_toList,
      List.getD_eq_getElem _ _ (by have : onThreeTreePts.toList.length = 90 := rfl; omega)]
  have eQ : onThreeTreePar[k]! = tQ k := by
    unfold tQ
    rw [getElem!_pos onThreeTreePar k (by have : onThreeTreePar.size = 90 := rfl; omega),
      List.getD_eq_getElem _ _ (by have : onThreeTreePar.toList.length = 90 := rfl; omega)]
    rfl
  have eG : onThreeTreeGen[k]! = tG k := by
    unfold tG
    rw [getElem!_pos onThreeTreeGen k (by have : onThreeTreeGen.size = 90 := rfl; omega),
      List.getD_eq_getElem _ _ (by have : onThreeTreeGen.toList.length = 90 := rfl; omega)]
    rfl
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, eP k hk, eQ, eG]
  refine ⟨h1, ?_⟩
  rcases h4 with h0 | ⟨hq, hg, he⟩
  · exact Or.inl h0
  · have hsz : onThreeYArrs.size = 2 := by simp [onThreeYArrs, onThreeY]
    refine Or.inr ⟨⟨hq, by omega⟩, ?_⟩
    rw [eP _ (by omega), yArr_get hg (tree_facts _ (by omega)).1, he]

theorem covers_check : onThreeCovers (onSevenArr [6]) onThreeTreePts = true := by
  unfold onThreeCovers
  have hlen : (onSevenGood (onSevenArr [6]) []).length = 90 := good_90
  have hnd : (onSevenGood (onSevenArr [6]) []).Nodup := (List.nodup_range).filter _
  have hmem : ∀ k < 90, tP k ∈ onSevenGood (onSevenArr [6]) [] := by
    intro k hk
    obtain ⟨h1, h2, -, -⟩ := tree_facts k hk
    unfold onSevenGood
    rw [List.mem_filter, List.mem_range]
    refine ⟨h1, ?_⟩
    rw [x_get h1, h2]
    simp
  have hinj : Set.InjOn tP (Finset.range 90 : Set Nat) := by
    intro a ha b hb e
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (tree_facts b hb).2.2.1 a h e
    · exact (tree_facts a ha).2.2.1 b h e.symm
  have hsub : (Finset.range 90).image tP ⊆ (onSevenGood (onSevenArr [6]) []).toFinset := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hq
    exact List.mem_toFinset.2 (hmem k (Finset.mem_range.1 hk))
  have heq : (Finset.range 90).image tP = (onSevenGood (onSevenArr [6]) []).toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [List.toFinset_card_of_nodup hnd, hlen, Finset.card_image_of_injOn hinj,
        Finset.card_range])
  refine List.all_eq_true.2 fun q hq => ?_
  have hq' : q ∈ (Finset.range 90).image tP := heq ▸ List.mem_toFinset.2 hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hq'
  rw [Array.contains_iff_mem, Array.mem_def]
  exact tP_mem (Finset.mem_range.1 hk)

theorem facts9702 : onThreeCommOK (onSevenArr [6]) = true ∧
    onThreeTreeOK onThreeYArrs onThreeTreePts onThreeTreePar onThreeTreeGen = true ∧
    onThreeCovers (onSevenArr [6]) onThreeTreePts = true :=
  ⟨comm_check, tree_check, covers_check⟩

end CertificateChecks.KernelSpor.ONS

end
