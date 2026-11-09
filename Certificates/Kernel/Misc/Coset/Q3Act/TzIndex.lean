module

public import Certificates.Kernel.Misc.Coset.Q3Act.Tz
import Certificates.Kernel.CosPres.F291372BA
import Certificates.Kernel.CosPres.F291372C
import CFSG.Certificates.Kernel.Misc.Coset.TableFactE
import CFSG.Certificates.Kernel.Misc.Coset.CentralIndex

public section

namespace CFSG.KAct.Q3

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

@[expose] def commW (i : ℕ) : List (Fin 12 × Bool) :=
  [(11, true), (Fin.ofNat 12 i, true), (11, false), (Fin.ofNat 12 i, false)]

theorem commW_check : (List.range 11).all (fun i =>
    (tzRels (tzGen CFSG.KD.OrdFi24p.rels) (wsQN CFSG.KD.OrdFi24p.rels)).contains (commW i)) =
      true := by
  decide +kernel

theorem zeta_central (g : PG 12 (tzRels (tzGen CFSG.KD.OrdFi24p.rels)
    (wsQN CFSG.KD.OrdFi24p.rels))) : PresentedGroup.of 11 * g = g * PresentedGroup.of 11 := by
  have hgen : ∀ i : Fin 12, Commute (PresentedGroup.of (11 : Fin 12) :
      PG 12 (tzRels (tzGen CFSG.KD.OrdFi24p.rels) (wsQN CFSG.KD.OrdFi24p.rels)))
      (PresentedGroup.of i) := by
    intro i
    by_cases hi : i.val < 11
    · have hm := List.all_eq_true.1 commW_check i.val (List.mem_range.2 hi)
      rw [List.contains_iff_mem] at hm
      have h1 : PresentedGroup.mk (pgRels (tzRels (tzGen CFSG.KD.OrdFi24p.rels)
          (wsQN CFSG.KD.OrdFi24p.rels))) (FreeGroup.mk (commW i.val)) = 1 :=
        PresentedGroup.one_of_mem (List.mem_map_of_mem (f := FreeGroup.mk) hm)
      have hi' : Fin.ofNat 12 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      have hw : FreeGroup.mk (commW i.val) = FreeGroup.of 11 * FreeGroup.of i *
          (FreeGroup.of 11)⁻¹ * (FreeGroup.of i)⁻¹ := by
        rw [commW, hi']
        rfl
      rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1
    · have hlt := i.isLt
      have : i = 11 := Fin.ext (by change i.val = 11; omega)
      rw [this]
  have hg : g ∈ Subgroup.closure (Set.range PresentedGroup.of) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact (hgen i).eq
  | one => rw [mul_one, one_mul]
  | mul x y _ _ hx hy => exact (Commute.mul_right hx hy).eq
  | inv x _ hx => exact (Commute.inv_right hx).eq

theorem genSub_index_tz12_le :
    (genSub (pgRels (tzRels (tzGen CFSG.KD.OrdFi24p.rels) (wsQN CFSG.KD.OrdFi24p.rels)))
        (subsetOf 12 S0)).FiniteIndex ∧
      (genSub (pgRels (tzRels (tzGen CFSG.KD.OrdFi24p.rels) (wsQN CFSG.KD.OrdFi24p.rels)))
        (subsetOf 12 S0)).index ≤ 920808 := by
  have hK := TableFactE.genSub_index (tzRels (tzGen CFSG.KD.OrdFi24p.rels)
    (wsQN CFSG.KD.OrdFi24p.rels)) (by norm_num) (subsetOf 12 [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11])
    CFSG.KBFact.F291372b
  have h := genSub_index_le_central (n := 3) (a := 11) (by norm_num) zeta_central
    CFSG.KBCube.F291372c.cube_mem (by decide +kernel) (by decide +kernel) (by decide +kernel) hK
  exact ⟨h.1, h.2.trans (by norm_num)⟩

end CFSG.KAct.Q3
