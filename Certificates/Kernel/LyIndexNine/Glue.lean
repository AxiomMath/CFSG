module

public import CFSG.Sporadic.Ly.IndexNineInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.MS2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
import Certificates.Kernel.LyIndexNine.Chk
import CFSG.Sporadic.Schreier.LyChain11

namespace CertificateChecks.KernelLy9

attribute [local instance] Finset.smulFinset Finset.mulActionFinset

open Subgroup CFSG.Sporadic.Ly CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.ComponentClassification.PSL3Four

theorem lyTab1 : TabRep (n := 11) lyGensA[0]! lyUG1 := ⟨by decide +kernel, by decide +kernel⟩
theorem lyTab2 : TabRep (n := 11) lyGensA[1]! lyUG2 := ⟨by decide +kernel, by decide +kernel⟩
theorem lyTab3 : TabRep (n := 11) lyGensA[2]! lyUG3 := ⟨by decide +kernel, by decide +kernel⟩

theorem lyGensA_size : lyGensA.size = 3 := rfl

noncomputable def lyU_gen : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure ({lyUG1, lyUG2, lyUG3} : Set (Equiv.Perm (Fin 11)))

theorem lyU_gen_eq :
    lyU_gen = Subgroup.closure ({lyUG1, lyUG2, lyUG3} : Set (Equiv.Perm (Fin 11))) := rfl

theorem lyU_gen_card : Nat.card lyU_gen = 128 := by
  obtain ⟨a1, a2, a3⟩ := (by simpa only [bAnd_iff] using ly_hd :
    gensK lyGensA 11 4 LYE.k LYE.G = true ∧ Nat.beq LYE.cnt 128 = true ∧
      penumHdK (pidn 11 4) LYE.cnt 128 LYE.T LYE.PL = true)
  have e : LYE.cnt = 128 := Nat.eq_of_beq_eq_true a2
  have hp : ∀ i < LYE.cnt, penumPtK 11 4 (mask 4) (11 * 4) false LYE.G LYE.GI LYE.k LYE.cnt
      LYE.T LYE.PL LYE.POS LYE.SRT LYE.SRI i = true := fun i hi =>
    penumSl_spec ly_sl i (Nat.zero_le _) (by omega) hi
  have hs := penumK_left_sound (cap := 128) (by decide) (gensOK_of a1) a3 hp
  have hA : ∀ a ∈ ({lyUG1, lyUG2, lyUG3} : Set (Equiv.Perm (Fin 11))),
      ∃ j < lyGensA.size, TabRep lyGensA[j]! a := by
    rintro a (rfl | rfl | rfl)
    · exact ⟨0, by rw [lyGensA_size]; omega, lyTab1⟩
    · exact ⟨1, by rw [lyGensA_size]; omega, lyTab2⟩
    · exact ⟨2, by rw [lyGensA_size]; omega, lyTab3⟩
  have hg : ∀ j < lyGensA.size, ∃ a ∈ ({lyUG1, lyUG2, lyUG3} : Set (Equiv.Perm (Fin 11))),
      TabRep lyGensA[j]! a := by
    intro j hj
    rw [lyGensA_size] at hj
    interval_cases j
    · exact ⟨lyUG1, Set.mem_insert _ _, lyTab1⟩
    · exact ⟨lyUG2, Set.mem_insert_of_mem _ (Set.mem_insert _ _), lyTab2⟩
    · exact ⟨lyUG3, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), lyTab3⟩
  have hEn := enumerates_closure hA hg hs.2
  rw [lyU_gen, hEn.card, penumRec_eq, Array.toList_ofFn, List.length_ofFn]
  exact e

theorem lyUG1_mem_alt : lyUG1 ∈ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
theorem lyUG2_mem_alt : lyUG2 ∈ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
theorem lyUG3_mem_alt : lyUG3 ∈ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem lyU_gen_le_alt : lyU_gen ≤ alternatingGroup (Fin 11) := by
  rw [lyU_gen_eq, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact lyUG1_mem_alt
  · exact lyUG2_mem_alt
  · exact lyUG3_mem_alt

noncomputable def lyA11U : Subgroup ↥(alternatingGroup (Fin 11)) :=
  lyU_gen.subgroupOf (alternatingGroup (Fin 11))

theorem lyU_card : Nat.card lyA11U = 128 := by
  rw [lyA11U, Nat.card_congr (Subgroup.subgroupOfEquivOfLe lyU_gen_le_alt).toEquiv,
    lyU_gen_card]

theorem lyUG1_fix : lyUG1 • lyX0 = lyX0 := by decide +kernel
theorem lyUG2_fix : lyUG2 • lyX0 = lyX0 := by decide +kernel
theorem lyUG3_fix : lyUG3 • lyX0 = lyX0 := by decide +kernel

theorem lyU_gen_le_stab : lyU_gen ≤ MulAction.stabilizer (Equiv.Perm (Fin 11)) lyX0 := by
  rw [lyU_gen_eq, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · simpa [MulAction.mem_stabilizer_iff] using lyUG1_fix
  · simpa [MulAction.mem_stabilizer_iff] using lyUG2_fix
  · simpa [MulAction.mem_stabilizer_iff] using lyUG3_fix

theorem lyU_fix (u : lyA11U) : (u : Equiv.Perm (Fin 11)) • lyX0 = lyX0 :=
  lyU_gen_le_stab u.2

theorem lyU_fix' (u : ↥(alternatingGroup (Fin 11))) (hu : u ∈ lyA11U) :
    (u : Equiv.Perm (Fin 11)) • lyX0 = lyX0 := by
  have h := lyU_fix (⟨u, hu⟩ : lyA11U)
  simpa using h

theorem lyAltFactorization : (19958400 : ℕ).factorization 2 = 7 := by
  rw [show (19958400 : ℕ) = 2 ^ 7 * 155925 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem lyU_isSylow : CFSG.QuasithinUnique.IsSylowTwoOf lyA11U ⊤ := by
  refine CFSG.QuasithinUnique.isSylowTwoOf_of_card_eq le_top ?_ ?_
  · exact IsPGroup.of_card (n := 7) (by rw [lyU_card]; norm_num)
  · rw [CFSG.QuasithinUnique.twoPart, Subgroup.card_top,
      CFSG.Sporadic.LySchreier.card_alternating_eleven, lyAltFactorization]
    exact lyU_card

theorem lyX_mem_alt : lyXPerm ∈ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
theorem lyY_mem_alt : lyYPerm ∈ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem lyX_fix : lyXPerm • lyX0 = lyX0 := by decide +kernel
theorem lyY_fix : lyYPerm • lyX0 = lyX0 := by decide +kernel

theorem lyX_pow : lyXPerm ^ 3 = 1 := by decide +kernel
theorem lyY_pow : lyYPerm ^ 3 = 1 := by decide +kernel
theorem lyXY_comm : Commute lyXPerm lyYPerm := by
  change lyXPerm * lyYPerm = lyYPerm * lyXPerm
  decide +kernel
theorem lyX_ne_one : lyXPerm ≠ 1 := by decide +kernel
theorem lyY_ne_one : lyYPerm ≠ 1 := by decide +kernel
theorem lyY_ne_X : lyYPerm ≠ lyXPerm := by decide +kernel
theorem lyY_ne_X2 : lyYPerm ≠ lyXPerm ^ 2 := by decide +kernel

theorem lyUGensPerm_mem_gen {g : Equiv.Perm (Fin 11)} (hg : g ∈ lyUGensPerm) : g ∈ lyU_gen := by
  simp only [lyUGensPerm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rw [lyU_gen_eq]
  exact Subgroup.subset_closure (by simpa using hg)

def lyColor (x : Fin 11) : Fin 4 :=
  if x ∈ lyA then 0 else if x ∈ lyB then 1 else if x ∈ lyBlockC then 2 else 3

theorem fiber_zero : {x : Fin 11 | lyColor x = 0} = (lyA : Set (Fin 11)) := by
  ext x; fin_cases x <;> simp [lyColor, lyA, lyB, lyBlockC, lyD]
theorem fiber_one : {x : Fin 11 | lyColor x = 1} = (lyB : Set (Fin 11)) := by
  ext x; fin_cases x <;> simp [lyColor, lyA, lyB, lyBlockC, lyD]
theorem fiber_two : {x : Fin 11 | lyColor x = 2} = (lyBlockC : Set (Fin 11)) := by
  ext x; fin_cases x <;> simp [lyColor, lyA, lyB, lyBlockC, lyD]
theorem fiber_three : {x : Fin 11 | lyColor x = 3} = (lyD : Set (Fin 11)) := by
  ext x; fin_cases x <;> simp [lyColor, lyA, lyB, lyBlockC, lyD]

theorem mem_lyA_iff (x : Fin 11) : x ∈ lyA ↔ lyColor x = 0 := by
  fin_cases x <;> decide
theorem mem_lyB_iff (x : Fin 11) : x ∈ lyB ↔ lyColor x = 1 := by
  fin_cases x <;> decide
theorem mem_lyC_iff (x : Fin 11) : x ∈ lyBlockC ↔ lyColor x = 2 := by
  fin_cases x <;> decide
theorem mem_lyD_iff (x : Fin 11) : x ∈ lyD ↔ lyColor x = 3 := by
  fin_cases x <;> decide

def lyHordSet : Set (Equiv.Perm (Fin 11)) := {g | lyColor ∘ g = lyColor}

theorem lyHordSet_ncard : lyHordSet.ncard = 1152 := by
  rw [lyHordSet, DomMulAct.stabilizer_ncard, Fin.prod_univ_four,
    fiber_zero, fiber_one, fiber_two, fiber_three,
    Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  decide

def lyHord : Subgroup (Equiv.Perm (Fin 11)) where
  carrier := lyHordSet
  mul_mem' := by
    intro a b ha hb
    change lyColor ∘ (a * b) = lyColor
    funext x
    rw [Function.comp_apply, Equiv.Perm.mul_apply]
    exact (congrFun ha (b x)).trans (congrFun hb x)
  one_mem' := by
    change lyColor ∘ (1 : Equiv.Perm (Fin 11)) = lyColor
    ext x; rfl
  inv_mem' := by
    intro a ha
    change lyColor ∘ (a⁻¹ : Equiv.Perm (Fin 11)) = lyColor
    funext x
    have hx := congrFun ha ((a⁻¹ : Equiv.Perm (Fin 11)) x)
    simpa using hx.symm

theorem lyHord_card : Nat.card ↥lyHord = 1152 := by
  have h := Nat.card_coe_set_eq (lyHord : Set (Equiv.Perm (Fin 11)))
  exact h.trans lyHordSet_ncard

theorem lySmulX0 (c : Equiv.Perm (Fin 11)) :
    c • lyX0 = {c • lyA, c • lyB, c • lyBlockC, c • lyD} := by
  simp [lyX0, Finset.smul_finset_def]

theorem card_smul_A (g : Equiv.Perm (Fin 11)) : (g • lyA).card = 4 := by
  rw [Finset.card_smul_finset]; decide
theorem card_smul_B (g : Equiv.Perm (Fin 11)) : (g • lyB).card = 4 := by
  rw [Finset.card_smul_finset]; decide
theorem card_smul_C (g : Equiv.Perm (Fin 11)) : (g • lyBlockC).card = 2 := by
  rw [Finset.card_smul_finset]; decide
theorem card_smul_D (g : Equiv.Perm (Fin 11)) : (g • lyD).card = 1 := by
  rw [Finset.card_smul_finset]; decide

theorem eq_A_or_B_of_mem_x0 {b : Finset (Fin 11)} (hb : b ∈ lyX0)
    (hcard : b.card = 4) : b = lyA ∨ b = lyB := by
  rw [lyX0] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso; rw [h] at hcard; revert hcard; decide
  · exfalso; rw [h] at hcard; revert hcard; decide

theorem eq_C_of_mem_x0 {b : Finset (Fin 11)} (hb : b ∈ lyX0)
    (hcard : b.card = 2) : b = lyBlockC := by
  rw [lyX0] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h | h | h
  · exfalso; rw [h] at hcard; revert hcard; decide
  · exfalso; rw [h] at hcard; revert hcard; decide
  · exact h
  · exfalso; rw [h] at hcard; revert hcard; decide

theorem eq_D_of_mem_x0 {b : Finset (Fin 11)} (hb : b ∈ lyX0)
    (hcard : b.card = 1) : b = lyD := by
  rw [lyX0] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h | h | h
  · exfalso; rw [h] at hcard; revert hcard; decide
  · exfalso; rw [h] at hcard; revert hcard; decide
  · exfalso; rw [h] at hcard; revert hcard; decide
  · exact h

theorem lyHord_preserves_A {g : Equiv.Perm (Fin 11)} (hg : g ∈ lyHord) :
    g • lyA = lyA := by
  rw [MS2.smul_finset_eq_self_iff]
  intro x
  have h := congrFun hg x
  rw [Function.comp_apply] at h
  rw [mem_lyA_iff x, mem_lyA_iff (g x), h]

theorem lyHord_preserves_B {g : Equiv.Perm (Fin 11)} (hg : g ∈ lyHord) :
    g • lyB = lyB := by
  rw [MS2.smul_finset_eq_self_iff]
  intro x
  have h := congrFun hg x
  rw [Function.comp_apply] at h
  rw [mem_lyB_iff x, mem_lyB_iff (g x), h]

theorem lyHord_preserves_C {g : Equiv.Perm (Fin 11)} (hg : g ∈ lyHord) :
    g • lyBlockC = lyBlockC := by
  rw [MS2.smul_finset_eq_self_iff]
  intro x
  have h := congrFun hg x
  rw [Function.comp_apply] at h
  rw [mem_lyC_iff x, mem_lyC_iff (g x), h]

theorem lyHord_preserves_D {g : Equiv.Perm (Fin 11)} (hg : g ∈ lyHord) :
    g • lyD = lyD := by
  rw [MS2.smul_finset_eq_self_iff]
  intro x
  have h := congrFun hg x
  rw [Function.comp_apply] at h
  rw [mem_lyD_iff x, mem_lyD_iff (g x), h]

theorem lyHord_le_H : lyHord ≤ MulAction.stabilizer (Equiv.Perm (Fin 11)) lyX0 := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff, lySmulX0]
  rw [lyHord_preserves_A hg, lyHord_preserves_B hg, lyHord_preserves_C hg,
    lyHord_preserves_D hg]
  rfl

theorem lyUG1_smul_A : lyUG1 • lyA = lyB := by decide +kernel
theorem lyUG1_smul_B : lyUG1 • lyB = lyA := by decide +kernel
theorem lyUG1_smul_C : lyUG1 • lyBlockC = lyBlockC := by decide +kernel
theorem lyUG1_smul_D : lyUG1 • lyD = lyD := by decide +kernel
theorem lyUG1_sq : lyUG1 * lyUG1 = 1 := by decide +kernel
theorem lyUG1_ne_one : lyUG1 ≠ 1 := by decide +kernel

theorem lyUG1_mem_H : lyUG1 ∈ MulAction.stabilizer (Equiv.Perm (Fin 11)) lyX0 := by
  simpa [MulAction.mem_stabilizer_iff] using lyUG1_fix

theorem lyUG1_not_mem_lyHord : lyUG1 ∉ lyHord := by
  intro h
  have hA := lyHord_preserves_A h
  rw [lyUG1_smul_A] at hA
  exact (by decide : lyA ≠ lyB) hA.symm

theorem lyColor_eq_zero {x : Fin 11} (hx : x ∈ lyA) : lyColor x = 0 := by
  rw [← mem_lyA_iff]; exact hx
theorem lyColor_eq_one {x : Fin 11} (hx : x ∈ lyB) : lyColor x = 1 := by
  rw [← mem_lyB_iff]; exact hx
theorem lyColor_eq_two {x : Fin 11} (hx : x ∈ lyBlockC) : lyColor x = 2 := by
  rw [← mem_lyC_iff]; exact hx
theorem lyColor_eq_three {x : Fin 11} (hx : x ∈ lyD) : lyColor x = 3 := by
  rw [← mem_lyD_iff]; exact hx

theorem mem_lyHord_of_blocks {g : Equiv.Perm (Fin 11)}
    (hA : g • lyA = lyA) (hB : g • lyB = lyB) (hC : g • lyBlockC = lyBlockC)
    (hD : g • lyD = lyD) : g ∈ lyHord := by
  have hxA := (MS2.smul_finset_eq_self_iff g lyA).mp hA
  have hxB := (MS2.smul_finset_eq_self_iff g lyB).mp hB
  have hxC := (MS2.smul_finset_eq_self_iff g lyBlockC).mp hC
  have hxD := (MS2.smul_finset_eq_self_iff g lyD).mp hD
  funext x
  rw [Function.comp_apply]
  have hx : x ∈ lyA ∨ x ∈ lyB ∨ x ∈ lyBlockC ∨ x ∈ lyD := by
    fin_cases x <;> decide
  rcases hx with hx | hx | hx | hx
  · rw [lyColor_eq_zero hx, lyColor_eq_zero ((hxA x).mp hx)]
  · rw [lyColor_eq_one hx, lyColor_eq_one ((hxB x).mp hx)]
  · rw [lyColor_eq_two hx, lyColor_eq_two ((hxC x).mp hx)]
  · rw [lyColor_eq_three hx, lyColor_eq_three ((hxD x).mp hx)]

theorem smul_finset_injective (g : Equiv.Perm (Fin 11)) :
    Function.Injective (fun s : Finset (Fin 11) => g • s) := by
  intro s t h
  have h' : s.image (g : Fin 11 → Fin 11) = t.image (g : Fin 11 → Fin 11) := by
    simpa [Finset.smul_finset_def] using h
  exact Finset.image_injective (f := (g : Fin 11 → Fin 11)) g.injective h'

theorem lyHord_mem_or (g : Equiv.Perm (Fin 11))
    (hg : g ∈ MulAction.stabilizer (Equiv.Perm (Fin 11)) lyX0) :
    g ∈ lyHord ∨ lyUG1 * g ∈ lyHord := by
  have hgX : g • lyX0 = lyX0 := by simpa [MulAction.mem_stabilizer_iff] using hg
  have hmemA : g • lyA ∈ lyX0 := by
    have h := Finset.smul_mem_smul_finset (a := g) (by rw [lyX0]; simp : lyA ∈ lyX0)
    rwa [hgX] at h
  have hA := eq_A_or_B_of_mem_x0 hmemA (card_smul_A g)
  have hmemB : g • lyB ∈ lyX0 := by
    have h := Finset.smul_mem_smul_finset (a := g) (by rw [lyX0]; simp : lyB ∈ lyX0)
    rwa [hgX] at h
  have hB := eq_A_or_B_of_mem_x0 hmemB (card_smul_B g)
  have hmemC : g • lyBlockC ∈ lyX0 := by
    have h := Finset.smul_mem_smul_finset (a := g) (by rw [lyX0]; simp : lyBlockC ∈ lyX0)
    rwa [hgX] at h
  have hC := eq_C_of_mem_x0 hmemC (card_smul_C g)
  have hmemD : g • lyD ∈ lyX0 := by
    have h := Finset.smul_mem_smul_finset (a := g) (by rw [lyX0]; simp : lyD ∈ lyX0)
    rwa [hgX] at h
  have hD := eq_D_of_mem_x0 hmemD (card_smul_D g)
  by_cases hcase : g • lyA = lyA
  · left
    have hB' : g • lyB = lyB := by
      rcases hB with hB | hB
      · exfalso
        have heq : g • lyB = g • lyA := by rw [hB, hcase]
        exact (by decide : lyB ≠ lyA) (smul_finset_injective g heq)
      · exact hB
    exact mem_lyHord_of_blocks hcase hB' hC hD
  · right
    have hAg : g • lyA = lyB := by
      rcases hA with h | h
      · exact absurd h hcase
      · exact h
    have hprodA : (lyUG1 * g) • lyA = lyA := by rw [mul_smul, hAg, lyUG1_smul_B]
    have hprodB : (lyUG1 * g) • lyB = lyB := by
      rcases hB with hB | hB
      · rw [mul_smul, hB, lyUG1_smul_A]
      · exfalso
        have heq : g • lyB = g • lyA := by rw [hB, hAg]
        exact (by decide : lyB ≠ lyA) (smul_finset_injective g heq)
    have hprodC : (lyUG1 * g) • lyBlockC = lyBlockC := by
      rw [mul_smul, hC, lyUG1_smul_C]
    have hprodD : (lyUG1 * g) • lyD = lyD := by
      rw [mul_smul, hD, lyUG1_smul_D]
    exact mem_lyHord_of_blocks hprodA hprodB hprodC hprodD

noncomputable def lyA11H : Subgroup (Equiv.Perm (Fin 11)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 11)) lyX0

noncomputable def lyA11K : Subgroup (Equiv.Perm (Fin 11)) :=
  lyHord ⊓ alternatingGroup (Fin 11)

theorem lyH_even_eq_sup :
    lyA11H ⊓ alternatingGroup (Fin 11) = lyA11K ⊔ Subgroup.zpowers lyUG1 := by
  apply le_antisymm
  · intro g hg
    have hgA : g ∈ alternatingGroup (Fin 11) := hg.2
    rcases lyHord_mem_or g hg.1 with h | h
    · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨h, hgA⟩)
    · have hprodA : lyUG1 * g ∈ alternatingGroup (Fin 11) :=
        Subgroup.mul_mem _ lyUG1_mem_alt hgA
      have hprod : lyUG1 * g ∈ lyA11K := Subgroup.mem_inf.mpr ⟨h, hprodA⟩
      have hg' : g = lyUG1 * (lyUG1 * g) := by rw [← mul_assoc, lyUG1_sq, one_mul]
      rw [hg', sup_comm]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers lyUG1) hprod
  · refine sup_le ?_ ?_
    · intro g hg
      exact Subgroup.mem_inf.mpr ⟨lyHord_le_H hg.1, hg.2⟩
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨lyUG1_mem_H, lyUG1_mem_alt⟩

theorem swap_89_mem_lyHord : Equiv.swap (8 : Fin 11) 9 ∈ lyHord := by
  funext x
  rw [Function.comp_apply]
  fin_cases x <;> decide

noncomputable def lySignHom : ↥lyHord →* ℤˣ :=
  Equiv.Perm.sign.comp lyHord.subtype

theorem lySignHom_ker : lySignHom.ker = lyA11K.subgroupOf lyHord := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact Subgroup.mem_inf.mpr ⟨g.2, Equiv.Perm.mem_alternatingGroup.mp h⟩
  · intro h
    exact Equiv.Perm.mem_alternatingGroup.mpr h.2

theorem lySignHom_range : lySignHom.range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rcases Int.units_eq_one_or x with rfl | rfl
  · exact Subgroup.one_mem _
  · refine ⟨⟨Equiv.swap (8 : Fin 11) 9, swap_89_mem_lyHord⟩, ?_⟩
    change Equiv.Perm.sign (Equiv.swap (8 : Fin 11) 9) = -1
    exact Equiv.Perm.sign_swap (by decide)

theorem lyCardUnitsInt : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

theorem lyK_card : Nat.card ↥lyA11K = 576 := by
  have hmul := Subgroup.card_ker_mul_card_range lySignHom
  rw [lySignHom_ker] at hmul
  have hker : Nat.card ↥(lyA11K.subgroupOf lyHord) = Nat.card ↥lyA11K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hker, lySignHom_range, Subgroup.card_top, lyCardUnitsInt, lyHord_card] at hmul
  omega

theorem lyUG1_conj_lyHord {x : Equiv.Perm (Fin 11)} (hx : x ∈ lyHord) :
    lyUG1 * x * lyUG1⁻¹ ∈ lyHord := by
  have hginv : lyUG1⁻¹ = lyUG1 := inv_eq_of_mul_eq_one_right lyUG1_sq
  refine mem_lyHord_of_blocks ?_ ?_ ?_ ?_
  · rw [hginv, mul_smul, mul_smul, lyUG1_smul_A, lyHord_preserves_B hx, lyUG1_smul_B]
  · rw [hginv, mul_smul, mul_smul, lyUG1_smul_B, lyHord_preserves_A hx, lyUG1_smul_A]
  · rw [hginv, mul_smul, mul_smul, lyUG1_smul_C, lyHord_preserves_C hx, lyUG1_smul_C]
  · rw [hginv, mul_smul, mul_smul, lyUG1_smul_D, lyHord_preserves_D hx, lyUG1_smul_D]

theorem lyUG1_mem_normalizer_lyK :
    lyUG1 ∈ Subgroup.normalizer (lyA11K : Set (Equiv.Perm (Fin 11))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhord : h ∈ lyHord := hh.1
    have hhA : h ∈ alternatingGroup (Fin 11) := hh.2
    refine Subgroup.mem_inf.mpr ⟨lyUG1_conj_lyHord hhord, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ lyUG1_mem_alt hhA)
      (Subgroup.inv_mem _ lyUG1_mem_alt)
  · intro hh
    have hhord : lyUG1 * h * lyUG1⁻¹ ∈ lyHord := hh.1
    have hhA : lyUG1 * h * lyUG1⁻¹ ∈ alternatingGroup (Fin 11) := hh.2
    have hconj := lyUG1_conj_lyHord hhord
    have hconjA : lyUG1 * (lyUG1 * h * lyUG1⁻¹) * lyUG1⁻¹ ∈ alternatingGroup (Fin 11) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ lyUG1_mem_alt hhA)
        (Subgroup.inv_mem _ lyUG1_mem_alt)
    have hinv : lyUG1⁻¹ = lyUG1 := inv_eq_of_mul_eq_one_right lyUG1_sq
    have hback : lyUG1 * (lyUG1 * h * lyUG1⁻¹) * lyUG1⁻¹ = h := by
      rw [hinv]
      rw [show lyUG1 * (lyUG1 * h * lyUG1) * lyUG1
          = (lyUG1 * lyUG1) * h * (lyUG1 * lyUG1) by noncomm_ring]
      rw [lyUG1_sq, one_mul, mul_one]
    rw [hback] at hconj hconjA
    exact Subgroup.mem_inf.mpr ⟨hconj, hconjA⟩

theorem lyUG1_order : orderOf lyUG1 = 2 :=
  orderOf_eq_prime lyUG1_sq lyUG1_ne_one

theorem mem_zpowers_lyUG1 {x : Equiv.Perm (Fin 11)} :
    x ∈ Subgroup.zpowers lyUG1 ↔ x = 1 ∨ x = lyUG1 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← zpow_mod_orderOf, lyUG1_order, Nat.cast_ofNat]
    rcases Int.emod_two_eq k with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem lyK_disjoint_zpowers : Disjoint lyA11K (Subgroup.zpowers lyUG1) := by
  rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [mem_zpowers_lyUG1] at hx
  rcases hx with ⟨hxK, hx1 | hxg⟩
  · exact hx1
  · exfalso
    exact lyUG1_not_mem_lyHord (hxg ▸ hxK.1)

theorem lyK_sup_zpowers_card :
    Nat.card ↥(lyA11K ⊔ Subgroup.zpowers lyUG1) = Nat.card lyA11K * 2 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer lyA11K
    (Subgroup.zpowers lyUG1) (Subgroup.zpowers_le.mpr lyUG1_mem_normalizer_lyK)
    lyK_disjoint_zpowers, Nat.card_zpowers, lyUG1_order]

theorem lyH_even_card :
    Nat.card ↥(lyA11H ⊓ alternatingGroup (Fin 11)) = 1152 := by
  rw [lyH_even_eq_sup, lyK_sup_zpowers_card, lyK_card]

theorem eq_A_or_B_of_mem (c : Equiv.Perm (Fin 11)) {b : Finset (Fin 11)}
    (hb : b ∈ c • lyX0) (hcard : b.card = 4) : b = c • lyA ∨ b = c • lyB := by
  rw [lySmulX0] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso; rw [h, card_smul_C] at hcard; omega
  · exfalso; rw [h, card_smul_D] at hcard; omega

theorem eq_C_of_mem (c : Equiv.Perm (Fin 11)) {b : Finset (Fin 11)}
    (hb : b ∈ c • lyX0) (hcard : b.card = 2) : b = c • lyBlockC := by
  rw [lySmulX0] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h | h | h
  · exfalso; rw [h, card_smul_A] at hcard; omega
  · exfalso; rw [h, card_smul_B] at hcard; omega
  · exact h
  · exfalso; rw [h, card_smul_D] at hcard; omega

theorem eq_D_of_mem (c : Equiv.Perm (Fin 11)) {b : Finset (Fin 11)}
    (hb : b ∈ c • lyX0) (hcard : b.card = 1) : b = c • lyD := by
  rw [lySmulX0] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h | h | h
  · exfalso; rw [h, card_smul_A] at hcard; omega
  · exfalso; rw [h, card_smul_B] at hcard; omega
  · exfalso; rw [h, card_smul_C] at hcard; omega
  · exact h

theorem disjoint_smul_AB (c : Equiv.Perm (Fin 11)) :
    Disjoint (c • lyA) (c • lyB) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  rw [Finset.mem_smul_finset] at hxA hxB
  obtain ⟨a, ha, rfl⟩ := hxA
  obtain ⟨b, hb, hb'⟩ := hxB
  have hba : b = a := c.injective hb'
  subst hba
  exact (Finset.disjoint_left.mp (by decide : Disjoint lyA lyB)) ha hb

theorem sdiff_smul_A (c : Equiv.Perm (Fin 11)) :
    c • lyO8 \ (c • lyA) = c • lyB := by
  rw [lyO8, Finset.smul_finset_union, Finset.union_comm (c • lyA) (c • lyB),
    Finset.union_sdiff_self]
  exact Finset.sdiff_eq_self_of_disjoint (disjoint_smul_AB c).symm

theorem sdiff_smul_B (c : Equiv.Perm (Fin 11)) :
    c • lyO8 \ (c • lyB) = c • lyA := by
  rw [lyO8, Finset.smul_finset_union, Finset.union_sdiff_self]
  exact Finset.sdiff_eq_self_of_disjoint (disjoint_smul_AB c)

theorem lyA_ne_lyB : lyA ≠ lyB := by decide

theorem smul_O8_of_smul_x0 (c u : Equiv.Perm (Fin 11))
    (hu : u • (c • lyX0) = c • lyX0) : u • (c • lyO8) = c • lyO8 := by
  have hmemA : u • (c • lyA) ∈ c • lyX0 := by
    have h : c • lyA ∈ c • lyX0 := by rw [lySmulX0]; simp
    have := Finset.smul_mem_smul_finset (a := u) h
    rwa [hu] at this
  have hmemB : u • (c • lyB) ∈ c • lyX0 := by
    have h : c • lyB ∈ c • lyX0 := by rw [lySmulX0]; simp
    have := Finset.smul_mem_smul_finset (a := u) h
    rwa [hu] at this
  have hA : u • (c • lyA) = c • lyA ∨ u • (c • lyA) = c • lyB :=
    eq_A_or_B_of_mem c hmemA (by rw [Finset.card_smul_finset, card_smul_A])
  have hB : u • (c • lyB) = c • lyA ∨ u • (c • lyB) = c • lyB :=
    eq_A_or_B_of_mem c hmemB (by rw [Finset.card_smul_finset, card_smul_B])
  have hne : u • (c • lyA) ≠ u • (c • lyB) := by
    intro h
    have h2 : c • lyA = c • lyB := by
      have := congrArg (fun s => u⁻¹ • s) h
      simpa using this
    have h3 : lyA = lyB := by
      have := congrArg (fun s => c⁻¹ • s) h2
      simpa using this
    exact lyA_ne_lyB h3
  calc u • (c • lyO8) = u • (c • (lyA ∪ lyB)) := by rw [lyO8]
    _ = u • (c • lyA ∪ c • lyB) := by rw [Finset.smul_finset_union]
    _ = u • (c • lyA) ∪ u • (c • lyB) := by rw [Finset.smul_finset_union]
    _ = c • lyA ∪ c • lyB := by
          rcases hA with hA | hA <;> rcases hB with hB | hB
          · exfalso; exact hne (hA.trans hB.symm)
          · rw [hA, hB]
          · rw [hA, hB, Finset.union_comm]
          · exfalso; exact hne (hA.trans hB.symm)
    _ = c • (lyA ∪ lyB) := by rw [Finset.smul_finset_union]
    _ = c • lyO8 := by rw [lyO8]

theorem smul_C_of_smul_x0 (c u : Equiv.Perm (Fin 11))
    (hu : u • (c • lyX0) = c • lyX0) : u • (c • lyBlockC) = c • lyBlockC := by
  have h : c • lyBlockC ∈ c • lyX0 := by rw [lySmulX0]; simp
  have hmem := Finset.smul_mem_smul_finset (a := u) h
  rw [hu] at hmem
  exact eq_C_of_mem c hmem (by rw [Finset.card_smul_finset, card_smul_C])

theorem smul_D_of_smul_x0 (c u : Equiv.Perm (Fin 11))
    (hu : u • (c • lyX0) = c • lyX0) : u • (c • lyD) = c • lyD := by
  have h : c • lyD ∈ c • lyX0 := by rw [lySmulX0]; simp
  have hmem := Finset.smul_mem_smul_finset (a := u) h
  rw [hu] at hmem
  exact eq_D_of_mem c hmem (by rw [Finset.card_smul_finset, card_smul_D])

theorem lyUInvariantCheck_spec {size : Nat} {target Y : Finset (Fin 11)}
    (h : lyUInvariantCheck size target () = true) (hY : Y.card = size)
    (hinv : ∀ g ∈ lyUGensPerm, g • Y = Y) : Y = target := by
  by_contra hne
  have hstable : (lyUGensPerm.all fun g => decide (g • Y = Y)) = true := by
    rw [List.all_eq_true]
    intro g hg
    rw [decide_eq_true_eq]
    exact hinv g hg
  have hmem : Y ∈ (((Finset.univ : Finset (Fin 11)).powerset.filter fun s =>
      s.card = size ∧ (lyUGensPerm.all fun g => decide (g • s = s)) = true).erase target) := by
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by simpa using hne, Finset.subset_univ _, hY, hstable⟩
  have hzero : (((Finset.univ : Finset (Fin 11)).powerset.filter fun s =>
      s.card = size ∧ (lyUGensPerm.all fun g => decide (g • s = s)) = true).erase target).card
      = 0 := by
    have := h
    rw [lyUInvariantCheck, beq_iff_eq] at this
    exact this
  rw [Finset.card_eq_zero] at hzero
  rw [hzero] at hmem
  simp at hmem

theorem lySplitCheck_spec (h : lySplitCheck () = true) {s : Finset (Fin 11)}
    (hs : s ⊆ lyO8) (hcard : s.card = 4) (h0 : (0 : Fin 11) ∈ s)
    (hstab : ∀ g ∈ lyUGensPerm, g • s = s ∨ g • s = lyO8 \ s) : s = lyA := by
  by_contra hne
  have hstable : lySplitStable s = true := by
    rw [lySplitStable, List.all_eq_true]
    intro g hg
    rw [Bool.or_eq_true]
    rcases hstab g hg with h1 | h1
    · left; rw [decide_eq_true_eq]; exact h1
    · right; rw [decide_eq_true_eq]; exact h1
  have hmem : s ∈ ((lyO8.powerset.filter fun t =>
      t.card = 4 ∧ (0 : Fin 11) ∈ t ∧ lySplitStable t = true).erase lyA) := by
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by simpa using hne, hs, hcard, h0, hstable⟩
  have hzero : ((lyO8.powerset.filter fun t =>
      t.card = 4 ∧ (0 : Fin 11) ∈ t ∧ lySplitStable t = true).erase lyA).card = 0 := by
    have := h
    rw [lySplitCheck, beq_iff_eq] at this
    exact this
  rw [Finset.card_eq_zero] at hzero
  rw [hzero] at hmem
  simp at hmem

theorem sdiff_O8_A : lyO8 \ lyA = lyB := by decide +kernel

theorem smul_split_of_smul_x0 (c u : Equiv.Perm (Fin 11))
    (hu : u • (c • lyX0) = c • lyX0) {s : Finset (Fin 11)}
    (hs : s = c • lyA ∨ s = c • lyB) :
    u • s = s ∨ u • s = c • lyO8 \ s := by
  have hmemA : u • (c • lyA) ∈ c • lyX0 := by
    have h : c • lyA ∈ c • lyX0 := by rw [lySmulX0]; simp
    have := Finset.smul_mem_smul_finset (a := u) h
    rwa [hu] at this
  have hmemB : u • (c • lyB) ∈ c • lyX0 := by
    have h : c • lyB ∈ c • lyX0 := by rw [lySmulX0]; simp
    have := Finset.smul_mem_smul_finset (a := u) h
    rwa [hu] at this
  have hA : u • (c • lyA) = c • lyA ∨ u • (c • lyA) = c • lyB :=
    eq_A_or_B_of_mem c hmemA (by rw [Finset.card_smul_finset, card_smul_A])
  have hB : u • (c • lyB) = c • lyA ∨ u • (c • lyB) = c • lyB :=
    eq_A_or_B_of_mem c hmemB (by rw [Finset.card_smul_finset, card_smul_B])
  rcases hs with rfl | rfl
  · rcases hA with hA | hA
    · exact Or.inl hA
    · exact Or.inr (hA.trans (sdiff_smul_A c).symm)
  · rcases hB with hB | hB
    · exact Or.inr (hB.trans (sdiff_smul_B c).symm)
    · exact Or.inl hB

theorem lyStab_unique (c : Equiv.Perm (Fin 11))
    (hc : ∀ u ∈ lyU_gen, u • (c • lyX0) = c • lyX0) : c • lyX0 = lyX0 := by
  have hY8 : c • lyO8 = lyO8 :=
    lyUInvariantCheck_spec ly_inv8 (by rw [Finset.card_smul_finset]; decide)
      (fun g hg => smul_O8_of_smul_x0 c g (hc g (lyUGensPerm_mem_gen hg)))
  have hY2 : c • lyBlockC = lyBlockC :=
    lyUInvariantCheck_spec ly_inv2 (by rw [Finset.card_smul_finset]; decide)
      (fun g hg => smul_C_of_smul_x0 c g (hc g (lyUGensPerm_mem_gen hg)))
  have hY1 : c • lyD = lyD :=
    lyUInvariantCheck_spec ly_inv1 (by rw [Finset.card_smul_finset]; decide)
      (fun g hg => smul_D_of_smul_x0 c g (hc g (lyUGensPerm_mem_gen hg)))
  let s : Finset (Fin 11) := if (0 : Fin 11) ∈ c • lyA then c • lyA else c • lyB
  have hsAB : s = c • lyA ∨ s = c • lyB := by
    unfold s
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hs_sub : s ⊆ lyO8 := by
    rcases hsAB with hs | hs
    · rw [hs, ← hY8]
      exact Finset.smul_finset_subset_smul_finset (by decide : lyA ⊆ lyO8)
    · rw [hs, ← hY8]
      exact Finset.smul_finset_subset_smul_finset (by decide : lyB ⊆ lyO8)
  have hs_card : s.card = 4 := by
    rcases hsAB with hs | hs
    · rw [hs, Finset.card_smul_finset]; decide
    · rw [hs, Finset.card_smul_finset]; decide
  have hs0 : (0 : Fin 11) ∈ s := by
    unfold s
    split_ifs with h
    · exact h
    · have h0O8 : (0 : Fin 11) ∈ c • lyO8 := by rw [hY8]; decide
      rw [lyO8, Finset.smul_finset_union] at h0O8
      rcases Finset.mem_union.mp h0O8 with h' | h'
      · exact absurd h' h
      · exact h'
  have hstab : ∀ g ∈ lyUGensPerm, g • s = s ∨ g • s = lyO8 \ s := by
    intro g hg
    have h := smul_split_of_smul_x0 c g (hc g (lyUGensPerm_mem_gen hg)) hsAB
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, hY8])
  have hs_eq : s = lyA := lySplitCheck_spec ly_split hs_sub hs_card hs0 hstab
  rcases hsAB with hs | hs
  · have hcA : c • lyA = lyA := by rw [← hs, hs_eq]
    have hcB : c • lyB = lyB := by
      have h : c • lyB = c • lyO8 \ c • lyA := (sdiff_smul_A c).symm
      rw [h, hY8, hcA]
      exact sdiff_O8_A
    calc c • lyX0 = {c • lyA, c • lyB, c • lyBlockC, c • lyD} := lySmulX0 c
      _ = {lyA, lyB, c • lyBlockC, c • lyD} := by rw [hcA, hcB]
      _ = {lyA, lyB, lyBlockC, lyD} := by rw [hY2, hY1]
      _ = lyX0 := rfl
  · have hcB : c • lyB = lyA := by rw [← hs, hs_eq]
    have hcA : c • lyA = lyB := by
      have h : c • lyA = c • lyO8 \ c • lyB := (sdiff_smul_B c).symm
      rw [h, hY8, hcB]
      exact sdiff_O8_A
    calc c • lyX0 = {c • lyA, c • lyB, c • lyBlockC, c • lyD} := lySmulX0 c
      _ = {lyB, lyA, c • lyBlockC, c • lyD} := by rw [hcA, hcB]
      _ = {lyA, lyB, c • lyBlockC, c • lyD} := by rw [Finset.insert_comm lyB lyA]
      _ = {lyA, lyB, lyBlockC, lyD} := by rw [hY2, hY1]
      _ = lyX0 := rfl

public theorem packageLy744104 :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IndexNinePackage
      ↥(alternatingGroup (Fin 11)) := by
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf lyA11U ⊤ := lyU_isSylow
  have hAut : ∀ α : MulAut ↥(alternatingGroup (Fin 11)),
      ∃ r ∈ (⊤ : Subgroup (Equiv.Perm (Fin 11))), ∀ n : ↥(alternatingGroup (Fin 11)),
        ((α n : ↥(alternatingGroup (Fin 11))) : Equiv.Perm (Fin 11)) = r * n * r⁻¹ := by
    intro α
    obtain ⟨r, hr⟩ :=
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11
        (by norm_num) (by norm_num)).2 α
    refine ⟨r, Subgroup.mem_top r, fun n => ?_⟩
    rw [← hr]
    exact MulAut.conjNormal_apply r n
  have hcard : Nat.card
      ((⊤ ⊓ MulAction.stabilizer (Equiv.Perm (Fin 11)) lyX0).subgroupOf
        (alternatingGroup (Fin 11))) = 9 * Nat.card lyA11U := by
    have htop : (⊤ ⊓ MulAction.stabilizer (Equiv.Perm (Fin 11)) lyX0) = lyA11H := by
      rw [lyA11H]; simp
    rw [htop]
    have hEq : lyA11H.subgroupOf (alternatingGroup (Fin 11)) =
        (lyA11H ⊓ alternatingGroup (Fin 11)).subgroupOf (alternatingGroup (Fin 11)) := by
      ext x
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_comm]
    rw [hEq, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : lyA11H ⊓ alternatingGroup (Fin 11) ≤
        alternatingGroup (Fin 11))).toEquiv, lyH_even_card, lyU_card]
  have hfix : ∀ u ∈ lyA11U, (u : Equiv.Perm (Fin 11)) • lyX0 = lyX0 :=
    fun u hu => lyU_fix' u hu
  have hyx : lyYPerm ∉ Subgroup.zpowers lyXPerm :=
    CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne lyX_pow lyY_ne_one lyY_ne_X lyY_ne_X2
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.indexNinePackage_of_unique_fixed
    (R := Equiv.Perm (Fin 11)) (N := alternatingGroup (Fin 11))
    (X := Finset (Finset (Fin 11))) (U := lyA11U) (A := ⊤) (C := ⊤) (x₀ := lyX0)
    hU hAut le_top le_top hfix
    (fun c _ hc => lyStab_unique c (fun u hu =>
      hc ⟨u, lyU_gen_le_alt hu⟩ (Subgroup.mem_subgroupOf.mpr hu))) hcard
    (x := lyXPerm) (y := lyYPerm) lyX_mem_alt lyY_mem_alt (Subgroup.mem_top _)
    (Subgroup.mem_top _) lyX_fix lyY_fix lyX_pow lyY_pow lyXY_comm lyX_ne_one hyx

end CertificateChecks.KernelLy9
