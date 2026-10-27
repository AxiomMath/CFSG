module

public import Certificates.Kernel.Misc.G23F3Facts
public import Certificates.Kernel.Misc.G2LiftChecks
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KD.Misc.G23F3

open CFSG.KS.Mat3 CFSG.KC.Misc.G23F3 CFSG.LieType.Multipliers.G23 CFSG.Sporadic.He.Native
open CFSG.LocalAnalysis.RankThreeTheoremC.G2Lift

theorem rootArrs_get (j : Fin 4) : rootArrs[j.val]! = rootArr j := by
  fin_cases j <;> rfl

theorem wordM_rootProd (w : List (Fin 4)) : wordM w = rootProd w := by
  unfold wordM rootProd
  induction w with
  | nil => simp only [List.foldr_nil]
  | cons j w ih => rw [List.foldr_cons, List.foldr_cons, ih, rootArrs_get]

theorem wordM_eq (w : List (Fin 4)) : wordM w = ofM3 (w.map rootMat).prod := by
  rw [wordM_rootProd, rootProd_eq]

theorem neOne_ofM3 {P : Matrix (Fin 14) (Fin 14) (ZMod 3)} (h : P ≠ 1) : neOne (ofM3 P) = true := by
  by_contra hn
  apply h
  ext i j
  have hn' : ∀ a < 14, ∀ b < 14, ((ofM3 P)[a]!)[b]! % 3 = if a = b then 1 else 0 := by
    simpa [neOne] using hn
  have e := hn' i.val i.isLt j.val j.isLt
  rw [ofM3_entry, Nat.mod_eq_of_lt (ZMod.val_lt _)] at e
  rw [Matrix.one_apply]
  apply ZMod.val_injective
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl] at e ⊢
    rw [e]
    rfl
  · have hij' : ¬ i.val = j.val := fun x => hij (Fin.ext x)
    rw [if_neg hij'] at e
    rw [if_neg hij, e]
    rfl

theorem liftCheck_true : liftCheck = true := by
  have h := lift_ok
  rw [CFSG.KS.PK.andB_eq, Bool.and_eq_true] at h
  obtain ⟨hc, hl⟩ := h
  obtain ⟨hE, hN⟩ := liftK_sound hc RK_canon
    (fun p hp => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
      exact ⟨lt_of_mem_map, lt_of_mem_map⟩)
    (fun w hw => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hw
      exact lt_of_mem_map) hl
  unfold liftCheck
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun p hp => ?_, fun w hw => ?_⟩
  · have e := hE _ (List.mem_map_of_mem (f := fun p => (p.1.map Fin.val, p.2.map Fin.val)) hp)
    simp only [map_RK] at e
    rw [beq_iff_eq, wordM_eq, wordM_eq, e]
  · have e := hN _ (List.mem_map_of_mem (f := List.map Fin.val) hw)
    rw [map_RK] at e
    rw [wordM_eq]
    exact neOne_ofM3 e

end CFSG.KD.Misc.G23F3

end
