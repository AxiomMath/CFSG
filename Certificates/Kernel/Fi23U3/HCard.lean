module

public import Certificates.Kernel.Fi23U3.HKb
public import Certificates.Kernel.Fi23U3.W6Pow
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

namespace CFSG.KD.Fi23H

open CFSG.SectionRank.Native CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe

local instance : NeZero fi23U3Cover3.m := ⟨by decide⟩

@[expose] def cover0 : List (List (Fin 4 × Bool)) :=
  coverWords fi23U3Cover3.rels fi23U3Cover3.cwF ++ cubeWords fi23U3Cover3.rels ++
    powWords fi23U3Cover3.ordF

theorem mem_cover {w : List (Fin 4 × Bool)} (hw : w ∈ cover0) : w ∈ fi23U3Cover3.cover := by
  rcases List.mem_append.1 hw with hw | hw
  · rcases List.mem_append.1 hw with hw | hw
    · exact mem_cover₃Words.2 (Or.inl hw)
    · exact mem_cover₃Words.2 (Or.inr (Or.inl hw))
  · exact mem_cover₃Words.2 (Or.inr (Or.inr hw))

@[expose] def w6 : List (Fin 3 × Bool) :=
  (List.replicate 6 [((1 : Fin 3), true), ((2 : Fin 3), true)]).flatten

@[expose] def rH : List (List (Fin 3 × Bool)) := restrictWords (subsetOf 4 [0, 1, 2]) cover0

@[expose] def rhW : List (List (Fin 3 × Bool)) := rH ++ [w6]

theorem rels_H_bool : (CFSG.KBRoute.F291381H.rels == rhW.map encW) = true := by
  quickRfl

theorem rels_L_bool :
    (CFSG.KBRoute.F291381L.rels == (restrictWords (subsetOf 3 [0, 2]) rhW).map encW) = true := by
  quickRfl

theorem rels_H : CFSG.KBRoute.F291381H.rels = rhW.map encW := beq_iff_eq.1 rels_H_bool

theorem rels_L : CFSG.KBRoute.F291381L.rels =
    (restrictWords (subsetOf 3 [0, 2]) rhW).map encW :=
  beq_iff_eq.1 rels_L_bool

theorem card_rhW : Finite (PG 3 rhW) ∧ Nat.card (PG 3 rhW) ≤ 8748 :=
  TableFact.card_restrict rhW (by norm_num) (subsetOf 3 [0, 2]) (by decide)
    (rels_H ▸ CFSG.KBFact.F291381H) (rels_L ▸ CFSG.KBFact.F291381L)

@[expose] noncomputable def gen (i : Fin 3) : PG 4 fi23U3Cover3.cover :=
  PresentedGroup.of ((subsetOf 4 [0, 1, 2]).get i)

theorem lift_mk (w : List (Fin 3 × Bool)) :
    FreeGroup.lift gen (FreeGroup.mk w) = PresentedGroup.mk _
      (FreeGroup.mk (w.map fun l => ((subsetOf 4 [0, 1, 2]).get l.1, l.2))) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul, ih,
      List.map_cons, show FreeGroup.mk (((subsetOf 4 [0, 1, 2]).get l.1, l.2) :: w.map
        (fun l => ((subsetOf 4 [0, 1, 2]).get l.1, l.2))) =
        FreeGroup.mk [((subsetOf 4 [0, 1, 2]).get l.1, l.2)] *
          FreeGroup.mk (w.map fun l => ((subsetOf 4 [0, 1, 2]).get l.1, l.2)) from rfl, map_mul]
    congr 1
    obtain ⟨j, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      rfl
    · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl, FreeGroup.lift_apply_of]
      rfl

theorem gen_one : gen 1 = PresentedGroup.of 1 := rfl

theorem gen_two : gen 2 = PresentedGroup.of 2 := rfl

theorem rels_one : ∀ r ∈ {r : FreeGroup (Fin 3) | r ∈ rhW.map FreeGroup.mk},
    FreeGroup.lift gen r = 1 := by
  intro r hr
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hr
  rcases List.mem_append.1 hw' with hw' | hw'
  · change w' ∈ List.filterMap (renumber (subsetOf 4 [0, 1, 2])) cover0 at hw'
    obtain ⟨w, hw, hren⟩ := List.mem_filterMap.1 hw'
    have h : (w'.map fun l => ((subsetOf 4 [0, 1, 2]).get l.1, l.2)) = w :=
      map_renumber (subsetOf 4 [0, 1, 2]) w w' hren
    rw [lift_mk, h]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_cover hw))
  rw [List.mem_singleton] at hw'
  subst hw'
  have h6 : FreeGroup.mk w6 = (FreeGroup.of 1 * FreeGroup.of 2) ^ 6 := by
    rw [w6, mk_flatten_replicate]
    rfl
  rw [h6, map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, gen_one, gen_two]
  exact CFSG.KD.Fi23W6.x1x2_pow_six

noncomputable def toPC : PG 3 rhW →* PG 4 fi23U3Cover3.cover :=
  PresentedGroup.toGroup rels_one

theorem toPC_of (i : Fin 3) : toPC (PresentedGroup.of i) = gen i :=
  PresentedGroup.toGroup.of rels_one

end CFSG.KD.Fi23H

end
