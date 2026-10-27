module

public import Certificates.Kernel.Misc.G23F3Roots
public import CFSG.Certificates.Kernel.Misc.G23F3Sound

public section

namespace CFSG.KD.Misc.G23F3

open CFSG.KS.Mat3 CFSG.KC.Misc.G23F3 CFSG.KC.G2Three CFSG.LieType.Multipliers.G23
open CFSG.Sporadic.He.Native CFSG.KC.Misc.G24 CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem rootArr_eq (j : Fin 4) : rootArr j = ofM3 (rootMat j) := rfl

theorem codeOf_getD (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) (i j : Fin 14) :
    (codeOf (ofM3 M)).getD (14 * i.val + j.val) 0 = (M i j).val := by
  have hi := i.isLt
  have hj := j.isLt
  have ht : 14 * i.val + j.val < 196 := by omega
  unfold codeOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some,
    Option.getD_some]
  have e1 : (14 * i.val + j.val) / 14 = i.val := by omega
  have e2 : (14 * i.val + j.val) % 14 = j.val := by omega
  rw [e1, e2, ofM3_entry]

theorem codeOf_canon (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    canon14 (codeOf (ofM3 M)) = true := by
  refine canon14_iff.2 ⟨by simp [codeOf], fun e he => ?_⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he
  have ht' := List.mem_range.1 ht
  have e := ofM3_entry M ⟨t / 14, by omega⟩ ⟨t % 14, by omega⟩
  simp only at e
  rw [e]
  exact ZMod.val_lt _

theorem dec14_codeOf (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) : dec14 (codeOf (ofM3 M)) = M := by
  ext i j
  simp only [dec14, Matrix.of_apply]
  rw [codeOf_getD]
  exact ZMod.natCast_zmod_val _

theorem nthV_eq : ∀ (l : List ℕ) (i : ℕ), nthV l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nthV_eq l i

theorem RK_nth (j : Fin 4) : nthV RK j.val = pkK (codeOf (rootArr j)) := by
  simp [RK, nthV_eq, List.getD_eq_getElem?_getD]

theorem RK_sound (j : Fin 4) :
    Canon3 196 (nthV RK j.val) ∧ mat3 14 196 (nthV RK j.val) = rootMat j := by
  rw [RK_nth, pkK_eq, rootArr_eq]
  exact ⟨pk_canon (codeOf_canon _), by rw [mat3_pk_eq (codeOf_canon _), dec14_codeOf]⟩

theorem RK_canon : ∀ j < 4, Canon3 196 (nthV RK j) := fun j hj => (RK_sound ⟨j, hj⟩).1

theorem map_RK (w : List (Fin 4)) :
    (w.map Fin.val).map (fun j => mat3 14 196 (nthV RK j)) = w.map rootMat := by
  rw [List.map_map]
  exact List.map_congr_left fun j _ => (RK_sound j).2

theorem lt_of_mem_map {w : List (Fin 4)} : ∀ j ∈ w.map Fin.val, j < 4 := by
  intro j hj
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hj
  exact k.isLt

theorem SK_sound (hc : constsK = true) (w : List (Fin 4)) :
    Canon3 196 (SK w) ∧ mat3 14 196 (SK w) = (w.map rootMat).prod := by
  obtain ⟨h1, h2⟩ := wordK_sound hc RK_canon (w.map Fin.val) lt_of_mem_map
  exact ⟨h1, by rw [SK, h2, map_RK]⟩

theorem rootProd_eq (w : List (Fin 4)) : rootProd w = ofM3 (w.map rootMat).prod := by
  induction w with
  | nil => exact idM3_eq
  | cons j w ih =>
    change mulM 3 14 (rootArr j) (rootProd w) = _
    rw [ih, mulM3_eq, rootArr_eq, toM3_ofM3, toM3_ofM3, List.map_cons, List.prod_cons]

end CFSG.KD.Misc.G23F3

end
