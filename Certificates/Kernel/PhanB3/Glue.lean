module

public import Certificates.Kernel.PhanB3.Walks
public import CFSG.Certificates.Kernel.Misc.Coset.MemWalk
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.ClassicalInvolution.Phan.Phan3B3Check
public import CFSG.ClassicalInvolution.Phan.Phan3B3TwistData
public import CFSG.ClassicalInvolution.Phan.Phan3B3Words
public import CFSG.ClassicalInvolution.Phan.Phan3KerA3
public import CFSG.ClassicalInvolution.Phan.Phan3Sp4Data
public import CFSG.ClassicalInvolution.Phan.Phan3D4Defs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelPhanB3

open CFSG.CosetTable CFSG.Certificates CFSG.KC.MiscCoset CFSG.ClassicalInvolution.Phan.Q3G

theorem card_of_fact {m : ℕ} (ws : List (List (Fin m × Bool))) (hm : m < 256)
    {rels words : List (List (ℕ × Bool))} {N : ℕ} (h : KB.TableFact m rels words N)
    (hr : ws.map encW = rels) (hw : words = []) : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ N := by
  subst hr hw
  exact TableFact.card ws hm h

theorem card_sp4 : Finite (PG 4 sp4Rels) ∧ Nat.card (PG 4 sp4Rels) ≤ 51840 :=
  card_of_fact _ (by norm_num) CFSG.KBFact.B3P (by decide +kernel) (by decide +kernel)

theorem card_sl3 : Finite (PG 4 sl3Rels) ∧ Nat.card (PG 4 sl3Rels) ≤ 5616 :=
  card_of_fact _ (by norm_num) CFSG.KBFact.B3L (by decide +kernel) (by decide +kernel)

theorem card_twist : ∀ p ∈ b3BadPairs,
    Finite (PG 6 (b3TwistRels p.1 p.2)) ∧ Nat.card (PG 6 (b3TwistRels p.1 p.2)) ≤ 1 := by
  intro p hp
  simp only [b3BadPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T0 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T1 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T2 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T3 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T4 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T5 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T6 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T7 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T8 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T9 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T10 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T11 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T12 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T13 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T14 (by decide +kernel) (by decide +kernel)
  · exact card_of_fact _ (by norm_num) CFSG.KBFact.B3T15 (by decide +kernel) (by decide +kernel)

theorem wordVal_of {m : ℕ} {ws : List (List (Fin m × Bool))} (w : List (Fin m × Bool)) :
    wordVal (fun i => (PresentedGroup.of i : PG m ws)) w =
      PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w) := by
  have hf : FreeGroup.lift (fun i => (PresentedGroup.of i : PG m ws)) =
      PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [← hf, FreeGroup.lift_mk]
  rfl

theorem wordVal_rel {w : List (Fin 8 × Bool)} (hw : w ∈ phanB3Rels) :
    wordVal (fun i => (PresentedGroup.of i : PhanB3Group)) w = 1 := by
  rw [wordVal_of]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem commute_of_rel {a b : Fin 8}
    (h : [(a, true), (b, true), (a, false), (b, false)] ∈ phanB3Rels) :
    Commute (PresentedGroup.of a : PhanB3Group) (PresentedGroup.of b) := by
  have e := wordVal_rel h
  simp only [wordVal, letterVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one] at e
  change _ * _ = _ * _
  calc (PresentedGroup.of a : PhanB3Group) * PresentedGroup.of b
      = (PresentedGroup.of a * (PresentedGroup.of b * ((PresentedGroup.of a)⁻¹ *
          (PresentedGroup.of b)⁻¹))) * (PresentedGroup.of b * PresentedGroup.of a) := by group
    _ = _ := by rw [e, one_mul]

@[expose] def swIdx : Fin 4 → Fin 8 := ![2, 3, 0, 1]

@[expose] def suIdx8 : Fin 4 → Fin 8 := ![0, 1, 2, 3]

theorem relsU_eq : (restrictWords (subsetOf 8 [0, 1, 2, 3]) phanB3Rels).map encW =
    CFSG.KBRoute.B3U.rels := by
  decide +kernel

theorem wordsU_eq : CFSG.KBRoute.B3U.T1.words = [] := by decide +kernel

theorem one_of_walkU {cs refs : List ℕ} (w : List (Fin 8 × Bool))
    (hs : (renumber (subsetOf 8 [0, 1, 2, 3]) w).isSome = true)
    (hc : (encW ((renumber (subsetOf 8 [0, 1, 2, 3]) w).get hs)).map Mem.codeN = cs)
    (hw : Mem.memOK CFSG.KBData.B3U.F 26132 cs refs = true) :
    PresentedGroup.mk {r | r ∈ phanB3Rels.map FreeGroup.mk} (FreeGroup.mk w) = 1 := by
  have h := CFSG.KBRoute.B3U.t1
  unfold CFSG.KBRoute.B3U.T1.ok at h
  exact mk_eq_one_of_walk phanB3Rels (S := subsetOf 8 [0, 1, 2, 3]) (by decide) relsU_eq h
    CFSG.KBRoute.B3U.top wordsU_eq w hs hc hw

theorem swapped_one : ∀ r ∈ su3Rels,
    wordVal (fun i => (PresentedGroup.of (swIdx i) : PhanB3Group)) r = 1 := by
  intro r hr
  rw [← wordVal_reindex (fun i => (PresentedGroup.of i : PhanB3Group)) swIdx r, wordVal_of]
  simp only [su3Rels, su3Codes, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_of_walkU _ (by decide +kernel) (by decide +kernel) walk0
  · exact one_of_walkU _ (by decide +kernel) (by decide +kernel) walk1
  · exact one_of_walkU _ (by decide +kernel) (by decide +kernel) walk2
  · exact one_of_walkU _ (by decide +kernel) (by decide +kernel) walk3
  · exact one_of_walkU _ (by decide +kernel) (by decide +kernel) walk4
  · exact one_of_walkU _ (by decide +kernel) (by decide +kernel) walk5

theorem decodeWord_su3 : ∀ c ∈ su3Codes,
    decodeWord 8 c = (decodeWord 4 c).map fun l => (suIdx8 l.1, l.2) := by
  decide +kernel

theorem su3_one : ∀ r ∈ su3Rels,
    wordVal (fun i => (PresentedGroup.of (suIdx8 i) : PhanB3Group)) r = 1 := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  rw [← wordVal_reindex (fun i => (PresentedGroup.of i : PhanB3Group)) suIdx8,
    ← decodeWord_su3 c hc]
  refine wordVal_rel (List.mem_append_left _ (List.mem_map_of_mem ?_))
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl hc)))

@[expose] noncomputable def b3w : PhanB3Group :=
  (PresentedGroup.of 5)⁻¹ * (PresentedGroup.of 4)⁻¹ * PresentedGroup.of 5

theorem commute_b3w {a : Fin 8} (h4 : [(a, true), (4, true), (a, false), (4, false)] ∈ phanB3Rels)
    (h5 : [(a, true), (5, true), (a, false), (5, false)] ∈ phanB3Rels) :
    Commute (PresentedGroup.of a : PhanB3Group) b3w := by
  have c4 := commute_of_rel h4
  have c5 := commute_of_rel h5
  exact (c5.inv_right.mul_right c4.inv_right).mul_right c5

theorem of_conj_b3w {a b : Fin 8}
    (h : [(b, false), (5, false), (4, false), (5, true), (a, true), (5, false), (4, true),
      (5, true)] ∈ phanB3Rels) :
    (PresentedGroup.of b : PhanB3Group) = b3w * PresentedGroup.of a * b3w⁻¹ := by
  have e := wordVal_rel h
  simp only [wordVal, letterVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one] at e
  rw [inv_mul_eq_one.1 e, b3w]
  group

@[expose] noncomputable def a3Gens : Fin 6 → PhanB3Group :=
  fun i => PresentedGroup.of (b3KerMap i)

theorem a3_of_mem {w : List (Fin 6 × Bool)} (h : b3KerWord w ∈ phanB3Rels) :
    wordVal a3Gens w = 1 :=
  (wordVal_reindex _ b3KerMap w).symm.trans (wordVal_rel h)

theorem a3Gens_rels : ∀ w ∈ phanA3Rels, wordVal a3Gens w = 1 := by
  intro w hw
  simp only [phanA3Rels, List.mem_append, List.mem_map] at hw
  rcases hw with (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | hw
  · rw [wordVal_map_shiftLetter]
    have h : (fun i => a3Gens (shiftIdx 0 (by decide) i)) =
        fun i => (PresentedGroup.of (swIdx i) : PhanB3Group) := by
      funext i
      fin_cases i <;> rfl
    rw [h]
    exact swapped_one r hr
  · rw [wordVal_map_shiftLetter]
    have h : (fun i => a3Gens (shiftIdx 2 (by decide) i)) =
        fun i => (MulAut.conj b3w).toMonoidHom (PresentedGroup.of (suIdx8 i) : PhanB3Group) := by
      funext i
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      fin_cases i
      · change (PresentedGroup.of 0 : PhanB3Group) = b3w * PresentedGroup.of 0 * b3w⁻¹
        rw [← (commute_b3w (a := 0) (by decide +kernel) (by decide +kernel)).eq]
        group
      · change (PresentedGroup.of 1 : PhanB3Group) = b3w * PresentedGroup.of 1 * b3w⁻¹
        rw [← (commute_b3w (a := 1) (by decide +kernel) (by decide +kernel)).eq]
        group
      · exact of_conj_b3w (a := 2) (b := 6) (by decide +kernel)
      · exact of_conj_b3w (a := 3) (b := 7) (by decide +kernel)
    rw [h, wordVal_map, su3_one r hr, map_one]
  · simp only [phanA3CommRels, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> exact a3_of_mem (by decide +kernel)

@[expose] noncomputable def a3Hom : PhanA3Group →* PhanB3Group := assignHom a3Gens a3Gens_rels

@[expose] noncomputable def u1 : PhanA3Group := PresentedGroup.mk _ (FreeGroup.mk phanA3U1)

@[expose] noncomputable def u2 : PhanA3Group := PresentedGroup.mk _ (FreeGroup.mk phanA3U2)

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
  have hA : a3Hom u1 = 1 := a3_of_mem (w := phanA3U1) (List.mem_append_right _ (by simp))
  have hB : a3Hom u2 = 1 := a3_of_mem (w := phanA3U2) (List.mem_append_right _ (by simp))
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
  rw [MonoidHom.mem_ker, he', map_mul, map_zpow, map_zpow, hA, hB, one_zpow, one_zpow, mul_one]

theorem card_range_le : Nat.card a3Hom.range ≤ 13063680 := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  have h1 : Nat.card a3Hom.range = a3Hom.ker.index :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange a3Hom).toEquiv).symm
  have h2 : phanP.ker.index = 13063680 := by
    rw [← card_su4]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective phanP phanP_surjective).toEquiv
  rw [h1, ← h2]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le ker_le)

theorem range_b3KerMap :
    Set.range b3KerMap = {x | x ∈ subsetOf 8 [0, 1, 2, 3, 6, 7]} := by
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  revert x
  decide +kernel

theorem range_a3Hom : a3Hom.range = genSub {r : FreeGroup (Fin 8) | r ∈ phanB3Rels.map FreeGroup.mk}
    (subsetOf 8 [0, 1, 2, 3, 6, 7]) := by
  rw [a3Hom, range_assignHom]
  change _ = Subgroup.closure
    ((fun x => PresentedGroup.of x) '' {x | x ∈ subsetOf 8 [0, 1, 2, 3, 6, 7]})
  rw [← range_b3KerMap, ← Set.range_comp]
  rfl

theorem card_le :
    Finite PhanB3Group ∧ Nat.card PhanB3Group ≤ 176904 * 51840 := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  obtain ⟨hfi, hidx⟩ := TableFact.genSub_index phanB3Rels (by norm_num)
    (subsetOf 8 [0, 1, 2, 3, 6, 7]) CFSG.KBFact.B3K
  rw [← range_a3Hom] at hfi hidx
  have hfinH : Finite a3Hom.range := Finite.of_surjective _ a3Hom.rangeRestrict_surjective
  have : Finite (PhanB3Group ⧸ a3Hom.range) := Subgroup.finite_quotient_of_finiteIndex
  have hfin : Finite PhanB3Group := Finite.of_subgroup_quotient a3Hom.range
  refine ⟨hfin, ?_⟩
  rw [← a3Hom.range.index_mul_card]
  calc a3Hom.range.index * Nat.card a3Hom.range ≤ 702 * 13063680 :=
        Nat.mul_le_mul hidx card_range_le
    _ = 176904 * 51840 := by norm_num

end CertificateChecks.KernelPhanB3

end
