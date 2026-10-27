module

public import Certificates.Kernel.Fi24.OctK
public import CFSG.Certificates.Kernel.Fi24.OctSound
public import CFSG.Sporadic.Fi24.OctadsInputs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi24.Oct

open CFSG.KC.Fi24Oct CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native Finset

theorem get!_eq (a : Array Nat) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  rw [← Array.getElem!_toList]
  simp only [getElem!_def, List.getD_eq_getElem?_getD]
  cases a.toList[i]? <;> rfl

theorem card_fin24 (p : Nat → Prop) [DecidablePred p] :
    (univ.filter fun i : Fin 24 => p i.val).card = ∑ i ∈ range 24, if p i then 1 else 0 := by
  rw [card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if p i then 1 else 0) 24

theorem len_masks : octMasks.toList.length = 759 := rfl

theorem len_par : octPar.toList.length = 759 := rfl

theorem len_lab : octLab.toList.length = 759 := rfl

theorem octF_card (k : Fin 759) : (octF k).card = 8 := by
  unfold octF
  rw [card_fin24 fun i => octMasks[k.val]!.testBit i = true, get!_eq]
  refine cardK_sound kA _ ?_
  rw [List.getD_eq_getElem _ _ (by rw [len_masks]; exact k.isLt)]
  exact List.getElem_mem _

theorem octF_inter (k k' : Fin 759) (h : k ≠ k') : (octF k ∩ octF k').card ≤ 4 := by
  unfold octF
  rw [← filter_and, card_fin24 fun i => octMasks[k.val]!.testBit i = true ∧
    octMasks[k'.val]!.testBit i = true, get!_eq, get!_eq]
  exact pairK_sound kB len_masks k.isLt k'.isLt (fun e => h (Fin.ext e))

theorem perm_get (l : Fin 2) (i : Nat) :
    (octPerms[l.val]!)[i]! =
      if l.val = 0 then (octPerms[0]!).toList.getD i 0 else (octPerms[1]!).toList.getD i 0 := by
  rcases l with ⟨_ | _ | l, hl⟩
  · simp [get!_eq]
  · simp [get!_eq]
  · omega

theorem octF_tree (k : Fin 759) (hk : k.val ≠ 0) :
    (octParF k).val < k.val ∧ octF k = (octF (octParF k)).image (permF (octLabF k)) := by
  obtain ⟨hp, hm⟩ := treeK_sound kC len_masks len_par len_lab hk k.isLt
  refine ⟨by simpa [octParF, get!_eq] using hp, ?_⟩
  ext x
  have hx := hm x.val x.isLt
  simp only [octF, mem_filter, mem_univ, true_and, mem_image]
  rw [get!_eq, hx]
  constructor
  · rintro ⟨i, hi, hb, he⟩
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · simpa [octParF, get!_eq] using hb
    · apply Fin.ext
      simp only [permF, octLabF, Fin.val_mk]
      rw [perm_get ⟨_, Nat.mod_lt _ (by norm_num)⟩ i, get!_eq]
      simpa using he
  · rintro ⟨y, hb, he⟩
    refine ⟨y.val, y.isLt, by simpa [octParF, get!_eq] using hb, ?_⟩
    have he' := congrArg Fin.val he
    simp only [permF, octLabF, Fin.val_mk] at he'
    rw [perm_get ⟨_, Nat.mod_lt _ (by norm_num)⟩ y.val, get!_eq] at he'
    simpa using he'

theorem octF_root_fix : octF 0 = (univ.filter fun i => permF 0 i = i) := by
  ext i
  simp only [octF, mem_filter, mem_univ, true_and]
  revert i
  decide +kernel

theorem octF_root : octF 0 = (octO0.map toFin24).toFinset := by
  ext i
  simp only [octF, mem_filter, mem_univ, true_and, List.mem_toFinset]
  revert i
  decide +kernel

theorem facts7023 :
    (∀ k, (octF k).card = 8) ∧
      (∀ k k', k ≠ k' → (octF k ∩ octF k').card ≤ 4) ∧
      (∀ k : Fin 759, k.val ≠ 0 →
        (octParF k).val < k.val ∧ octF k = (octF (octParF k)).image (permF (octLabF k))) ∧
      octF 0 = (Finset.univ.filter fun i => permF 0 i = i) ∧
      octF 0 = (octO0.map toFin24).toFinset :=
  ⟨octF_card, octF_inter, octF_tree, octF_root_fix, octF_root⟩

end CertificateChecks.KernelFi24.Oct

end
