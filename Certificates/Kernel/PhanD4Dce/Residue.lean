module

public import CFSG.ClassicalInvolution.Phan.Phan3KerA3
public import CFSG.ClassicalInvolution.Phan.Phan3D4Defs
public import CFSG.ClassicalInvolution.Phan.Phan3B3Words

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G

@[expose] noncomputable def phanR : Subgroup PhanD4Group :=
  Subgroup.closure (Set.range fun i : Fin 6 => (PresentedGroup.of (Fin.castLE (by decide) i) : PhanD4Group))

theorem wordVal_of {m : ℕ} {ws : List (List (Fin m × Bool))} (w : List (Fin m × Bool)) :
    wordVal (fun i => (PresentedGroup.of i : PG m ws)) w =
      PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w) := by
  have hf : FreeGroup.lift (fun i => (PresentedGroup.of i : PG m ws)) =
      PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [← hf, FreeGroup.lift_mk]
  rfl

theorem wordVal_rel {w : List (Fin 8 × Bool)} (hw : w ∈ phanD4Rels) :
    wordVal (fun i => (PresentedGroup.of i : PhanD4Group)) w = 1 := by
  rw [wordVal_of]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

@[expose] noncomputable def a3Gens : Fin 6 → PhanD4Group :=
  fun i => PresentedGroup.of (Fin.castLE (by decide) i)

theorem liftWord68_eq (w : List (Fin 6 × Bool)) :
    liftWord68 w = w.map fun l => (Fin.castLE (by decide) l.1, l.2) := rfl

theorem a3_of_mem {w : List (Fin 6 × Bool)} (h : liftWord68 w ∈ phanD4Rels) :
    wordVal a3Gens w = 1 := by
  rw [liftWord68_eq] at h
  exact (wordVal_reindex (fun i => (PresentedGroup.of i : PhanD4Group)) _ w).symm.trans (wordVal_rel h)

theorem liftWord68_mem : ∀ w ∈ phanA3Rels, liftWord68 w ∈ phanD4Rels := by
  decide +kernel

@[expose] noncomputable def a3Hom : PhanA3Group →* PhanD4Group :=
  assignHom a3Gens fun w hw => a3_of_mem (liftWord68_mem w hw)

@[expose] noncomputable def u1 : PhanA3Group := PresentedGroup.mk _ (FreeGroup.mk phanA3U1)

@[expose] noncomputable def u2 : PhanA3Group := PresentedGroup.mk _ (FreeGroup.mk phanA3U2)

theorem a3Hom_u1 : a3Hom u1 = 1 :=
  (assignHom_mk _ _ _).trans (a3_of_mem (w := phanA3U1) (List.mem_append_right _ (by simp)))

theorem a3Hom_u2 : a3Hom u2 = 1 :=
  (assignHom_mk _ _ _).trans (a3_of_mem (w := phanA3U2) (List.mem_append_right _ (by simp)))

theorem u_ne_one {s t : Int}
    (hs : -2 ≤ s ∧ s ≤ 2) (ht : -2 ≤ t ∧ t ≤ 2) (h : (s, t) ≠ (0, 0)) : u1 ^ s * u2 ^ t ≠ 1 := by
  intro h1
  have hw : (powWord phanA3U1 s ++ powWord phanA3U2 t, 3) ∈ phanA3KernelWords :=
    List.mem_map.mpr ⟨(s, t), mem_phanA3Exps hs ht h, rfl⟩
  have h3 := three_dvd_orderOf_phanA3 hw
  rw [mk_append, mk_powWord, mk_powWord] at h3
  change 3 ∣ orderOf (u1 ^ s * u2 ^ t) at h3
  rw [h1, orderOf_one] at h3
  omega

theorem ker_le : phanP.ker ≤ a3Hom.ker := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  let f : Fin 3 × Fin 3 → phanP.ker := fun ij =>
    ⟨u1 ^ (ij.1.val : ℤ) * u2 ^ (ij.2.val : ℤ), by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, map_zpow, u1, u2, phanP_mk_u1, phanP_mk_u2,
        one_zpow, one_zpow, mul_one]⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have h : u1 ^ (i.val : ℤ) * u2 ^ (j.val : ℤ) =
        u1 ^ (i'.val : ℤ) * u2 ^ (j'.val : ℤ) := congrArg Subtype.val hij
    have h1 : u1 ^ ((i.val : ℤ) - i'.val) * u2 ^ ((j.val : ℤ) - j'.val) = 1 := by
      calc u1 ^ ((i.val : ℤ) - i'.val) * u2 ^ ((j.val : ℤ) - j'.val)
          = u1 ^ (-(i'.val : ℤ)) * (u1 ^ (i.val : ℤ) * u2 ^ (j.val : ℤ)) *
              u2 ^ (-(j'.val : ℤ)) := by group
        _ = u1 ^ (-(i'.val : ℤ)) * (u1 ^ (i'.val : ℤ) * u2 ^ (j'.val : ℤ)) *
              u2 ^ (-(j'.val : ℤ)) := by rw [h]
        _ = 1 := by group
    by_contra hne
    have hi := i.isLt
    have hi' := i'.isLt
    have hj := j.isLt
    have hj' := j'.isLt
    refine u_ne_one (s := (i.val : ℤ) - i'.val) (t := (j.val : ℤ) - j'.val)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ?_ h1
    intro hst
    simp only [Prod.mk.injEq] at hst
    obtain ⟨hs0, ht0⟩ := hst
    have e1 : i = i' := Fin.ext (by omega)
    have e2 : j = j' := Fin.ext (by omega)
    exact hne (by rw [e1, e2])
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [card_ker_eq]; simp)
  intro e he
  obtain ⟨⟨i, j⟩, hij⟩ := hbij.2 ⟨e, he⟩
  have he' : e = u1 ^ (i.val : ℤ) * u2 ^ (j.val : ℤ) := (congrArg Subtype.val hij).symm
  rw [MonoidHom.mem_ker, he', map_mul, map_zpow, map_zpow, a3Hom_u1, a3Hom_u2, one_zpow,
    one_zpow, mul_one]

theorem range_a3Hom : a3Hom.range = phanR := by
  rw [a3Hom, range_assignHom]
  rfl

theorem card_phanR_le : Nat.card phanR ≤ 13063680 := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  have h1 : Nat.card a3Hom.range = a3Hom.ker.index :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange a3Hom).toEquiv).symm
  have h2 : phanP.ker.index = 13063680 := by
    rw [← card_su4]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective phanP phanP_surjective).toEquiv
  rw [← range_a3Hom, h1, ← h2]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le ker_le)

end CFSG.KD.PhanD4Dce

end
