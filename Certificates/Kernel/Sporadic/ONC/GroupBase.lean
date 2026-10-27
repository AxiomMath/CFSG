
module

public import Certificates.Kernel.Sporadic.ON2.Split
public import CFSG.Sporadic.Bridge.ONSurjBase
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelSpor.ONC

open Matrix CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Bridge
open CFSG.Sporadic.Bridge.ON CFSG.Sporadic.Bridge.ONGPL.Native TauCeti CFSG.Sporadic.ON.Kernel

theorem facts : matrixChecks () = true ∧
    CFSG.Sporadic.ON.Native.orbitOK nPts (colsA ()) (colsB ()) (orbitData ()) posOrb 3 = true ∧
    negOK nPts (orbitData ()) (negTable (orbitData ()) posOrb) = true ∧
    basisChecks (basisRows (orbitData ())) basisXLit = true ∧
    supportChecks (orbitData ()) (basisRows (orbitData ())) basisXLit = true ∧
    invOK nPts (orbitData ()).alpha (invT nPts (orbitData ()).alpha) = true ∧
    invOK nPts (orbitData ()).beta (invT nPts (orbitData ()).beta) = true :=
  CertificateChecks.KernelSpor.ON2.facts272164

theorem mA_sq : mA * mA = 1 := by
  have h := facts.1
  unfold matrixChecks at h
  simp only [Bool.and_eq_true] at h
  have e := toMat_eq_of_eqM h.1
  rwa [toMat_mul rowsA_size rowsWF_rowsA rowsWF_rowsA, toMat_idM, toMat_rowsA] at e

theorem mB_pow : mB ^ 4 = 1 := by
  have h := facts.1
  unfold matrixChecks at h
  simp only [Bool.and_eq_true] at h
  have e := toMat_eq_of_eqM h.2
  rwa [(powM_facts rowsWF_rowsB 4).2.2, toMat_idM, toMat_rowsB] at e

theorem det_mA : mA.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det mA_sq
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_mB : mB.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det mB_pow
  rw [Matrix.det_pow, h, Matrix.det_one, zero_pow (by norm_num)] at this
  exact zero_ne_one this

noncomputable abbrev gA0 : GL (Fin 154) (ZMod 3) := Matrix.GeneralLinearGroup.mkOfDetNeZero mA det_mA

noncomputable abbrev gB0 : GL (Fin 154) (ZMod 3) := Matrix.GeneralLinearGroup.mkOfDetNeZero mB det_mB

noncomputable abbrev J0 : Subgroup (GL (Fin 154) (ZMod 3)) := Subgroup.closure {gA0, gB0}

@[expose] noncomputable def ga0 : J0 := ⟨gA0, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def gb0 : J0 := ⟨gB0, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mat0 (g : J0) : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  ((g : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3))

theorem mat0_mul (g h : J0) : mat0 (g * h) = mat0 g * mat0 h := rfl

theorem mat0_one : mat0 (1 : J0) = 1 := rfl

theorem mat0_injective : Function.Injective mat0 := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat0_ga : mat0 ga0 = mA := rfl

theorem mat0_gb : mat0 gb0 = mB := rfl

theorem closure_gab0 : Subgroup.closure ({ga0, gb0} : Set J0) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA0, gB0} : Set (GL (Fin 154) (ZMod 3)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [ga0, gb0]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

theorem smul_vec0 (g : J0) (v : Vec) : g • v = mat0 g *ᵥ v := rfl

theorem orbit_parts : (orbitData ()).keys.size = nPts ∧ (orbitData ()).alpha.size = nPts ∧
    (orbitData ()).beta.size = nPts ∧
    ∀ i < nPts, canon154 (orbitData ()).keys[i]! = true ∧ posOrb (orbitData ()).keys[i]! = i ∧
      ap (orbitData ()).alpha i < nPts ∧
      (orbitData ()).keys[ap (orbitData ()).alpha i]! = mulVecT (colsA ()) (orbitData ()).keys[i]! ∧
      ap (orbitData ()).beta i < nPts ∧
      (orbitData ()).keys[ap (orbitData ()).beta i]! = mulVecT (colsB ()) (orbitData ()).keys[i]! := by
  have h := facts.2.1
  unfold CFSG.Sporadic.ON.Native.orbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_⟩
  have := parAll_eq_true h4 i hi
  simp only [CFSG.Sporadic.ON.Native.orbitCheckAt, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  obtain ⟨⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := this
  exact ⟨h5, h6, h7, h8, h9, h10⟩

theorem keys_wf0 {i : ℕ} (hi : i < nPts) : (orbitData ()).keys[i]!.toV.wf = true :=
  wf_of_canon154 (orbit_parts.2.2.2 i hi).1

theorem P_injective0 : ∀ i < nPts, ∀ j < nPts, P i = P j → i = j := by
  intro i hi j hj h
  have hi' := orbit_parts.2.2.2 i hi
  have hj' := orbit_parts.2.2.2 j hj
  have e := vecOf_inj hi'.1 hj'.1 h
  rw [← hi'.2.1, ← hj'.2.1]
  exact congrArg posOrb e

theorem ga_smul_P0 : ∀ i < nPts, ap (orbitData ()).alpha i < nPts ∧
    ga0 • P i = P (ap (orbitData ()).alpha i) := by
  intro i hi
  obtain ⟨hc, -, hlt, he, -, -⟩ := orbit_parts.2.2.2 i hi
  refine ⟨hlt, ?_⟩
  rw [smul_vec0, mat0_ga, ← toMat_rowsA, P, P, he]
  unfold colsA
  exact (vecOf_mulVecT (rowsA ()) (wf_of_canon154 hc)).symm

theorem gb_smul_P0 : ∀ i < nPts, ap (orbitData ()).beta i < nPts ∧
    gb0 • P i = P (ap (orbitData ()).beta i) := by
  intro i hi
  obtain ⟨hc, -, -, -, hlt, he⟩ := orbit_parts.2.2.2 i hi
  refine ⟨hlt, ?_⟩
  rw [smul_vec0, mat0_gb, ← toMat_rowsB, P, P, he]
  unfold colsB
  exact (vecOf_mulVecT (rowsB ()) (wf_of_canon154 hc)).symm

theorem smul_mem_ptSet0 (g : J0) : ∀ v ∈ ptSet, g • v ∈ ptSet := by
  refine smul_mem_of_closure closure_gab0 ((Set.finite_Iio nPts).image _) ?_ ?_ g
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (ga_smul_P0 i hi).1, (ga_smul_P0 i hi).2.symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (gb_smul_P0 i hi).1, (gb_smul_P0 i hi).2.symm⟩

@[expose] noncomputable def ptSub0 : SubMulAction J0 Vec where
  carrier := ptSet
  smul_mem' g _ hv := smul_mem_ptSet0 g _ hv

@[expose] noncomputable def ptEquiv0 : Fin nPts ≃ ptSub0 :=
  Equiv.ofBijective (fun i => ⟨P i, ⟨i, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (P_injective0 i i.isLt j j.isLt (congrArg Subtype.val h)), by
      rintro ⟨v, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi⟩, rfl⟩⟩

theorem ptEquiv0_apply (i : Fin nPts) : (ptEquiv0 i : Vec) = P i := rfl

noncomputable instance idxAction0 : MulAction J0 (Fin nPts) := ptEquiv0.mulAction J0

theorem smul_def0 (g : J0) (i : Fin nPts) : g • i = ptEquiv0.symm (g • ptEquiv0 i) := rfl

theorem ptEquiv0_smul (g : J0) (i : Fin nPts) : ptEquiv0 (g • i) = g • ptEquiv0 i := by
  rw [smul_def0, Equiv.apply_symm_apply]

theorem P_smul0 (g : J0) (i : Fin nPts) : P (g • i).val = g • P i.val := by
  have := congrArg Subtype.val (ptEquiv0_smul g i)
  rwa [ptEquiv0_apply, SubMulAction.val_smul, ptEquiv0_apply] at this

theorem idx_eq_iff0 {g : J0} {i j : ℕ} (hi : i < nPts) (hj : j < nPts) :
    idx nPts g i = j ↔ g • P i = P j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    rw [← P_smul0 g ⟨i, hi⟩, h]
  · intro h
    apply P_injective0 _ (g • (⟨i, hi⟩ : Fin nPts)).isLt _ hj
    rw [P_smul0 g ⟨i, hi⟩]
    exact h

theorem rep_ga0 : Rep nPts (orbitData ()).alpha ga0 := by
  intro i hi
  symm
  exact (idx_eq_iff0 hi (ga_smul_P0 i hi).1).2 (ga_smul_P0 i hi).2

theorem rep_gb0 : Rep nPts (orbitData ()).beta gb0 := by
  intro i hi
  symm
  exact (idx_eq_iff0 hi (gb_smul_P0 i hi).1).2 (gb_smul_P0 i hi).2

theorem basis_parts0 : chainQ.size = 154 ∧ (∀ t < chainQ.size, chainQ[t]! < nPts) ∧
    basisXLit.size = 154 ∧ (∀ x ∈ basisXLit, x.wf = true) ∧
    mulW 154 basisXLit (basisRows (orbitData ())) = idW 154 := by
  have h := facts.2.2.2.1
  unfold basisChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun t ht => ?_, h3, fun x hx => ?_, h5⟩
  · rw [getElem!_pos chainQ t ht]; simpa using h2 t ht
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact h4 i hi

theorem chainQ_lt0 {t : ℕ} (ht : t < chainQ.size) : chainQ[t]! < nPts := basis_parts0.2.1 t ht

theorem basisR_getElem0 {t : ℕ} (ht : t < 154) :
    (basisRows (orbitData ()))[t]! = (orbitData ()).keys[chainQ[t]!]! := by
  have ht' : t < chainQ.size := by rw [basis_parts0.1]; exact ht
  unfold basisRows
  rw [getElem!_pos _ t (by rw [Array.size_map]; exact ht'), Array.getElem_map,
    getElem!_pos chainQ t ht']

theorem basisR_size0 : (basisRows (orbitData ())).size = 154 := by
  unfold basisRows; rw [Array.size_map, basis_parts0.1]

theorem rowsWF_basisR0 : RowsWF (toVM (basisRows (orbitData ()))) := by
  intro t
  rw [toVM_getElem!]
  by_cases ht : t < 154
  · rw [basisR_getElem0 ht]
    exact keys_wf0 (chainQ_lt0 (by rw [basis_parts0.1]; exact ht))
  · rw [getElem!_neg _ t (by rw [basisR_size0]; exact ht), W.toV_default]
    exact V.wf_zero

theorem rowsWF_basisX0 : RowsWF (toVM basisXLit) := by
  intro t
  rw [toVM_getElem!]
  by_cases ht : t < basisXLit.size
  · rw [getElem!_pos basisXLit t ht]
    exact W.wf_spec (basis_parts0.2.2.2.1 _ (Array.getElem_mem ht))
  · rw [getElem!_neg basisXLit t ht, W.toV_default]
    exact V.wf_zero

theorem Xmat_mul_Umat0 :
    toMat 154 (toVM basisXLit) * toMat 154 (toVM (basisRows (orbitData ()))) = 1 := by
  have e := congrArg (fun Y => toMat 154 (toVM Y)) basis_parts0.2.2.2.2
  rwa [toVM_mulW, toVM_idW (by norm_num), toMat_idM,
    toMat_mul (by rw [toVM_size]; exact basis_parts0.2.2.1) rowsWF_basisX0 rowsWF_basisR0] at e

theorem Umat_row0 (t : Fin 154) :
    toMat 154 (toVM (basisRows (orbitData ()))) t = P chainQ[t.val]! := by
  funext j
  change toMat 154 (toVM (basisRows (orbitData ()))) t j = vecOf (orbitData ()).keys[chainQ[t.val]!]! j
  rw [toMat_apply, toVM_getElem!, basisR_getElem0 t.isLt]
  rfl

theorem sep0 (g : J0) (hg : ∀ t < chainQ.size, idx nPts g chainQ[t]! = chainQ[t]!) : g = 1 := by
  apply mat0_injective
  rw [mat0_one, ← one_smul (ZMod 3) (1 : Matrix (Fin 154) (Fin 154) (ZMod 3))]
  apply eq_smul_one_of_rows Xmat_mul_Umat0
  intro t
  have ht : t.val < chainQ.size := by rw [basis_parts0.1]; exact t.isLt
  rw [Umat_row0, one_smul, ← smul_vec0]
  exact (idx_eq_iff0 (chainQ_lt0 ht) (chainQ_lt0 ht)).1 (hg t.val ht)

theorem eq_of_tupleEq0 {g h : J0} {X Y : Table} (hX : Rep nPts X g) (hY : Rep nPts Y h)
    (e : tupleEq (apT X chainQ) (apT Y chainQ) = true) : g = h := by
  have : h⁻¹ * g = 1 := by
    apply sep0
    intro t ht
    simp only [tupleEq, Bool.and_eq_true, beq_iff_eq, apT_size] at e
    have := (allIn_eq_true.1 e.2) t (Nat.zero_le _) ht
    simp only [beq_iff_eq] at this
    rw [apT_get _ _ ht, apT_get _ _ ht, hX _ (chainQ_lt0 ht), hY _ (chainQ_lt0 ht)] at this
    rw [idx_mul, this, idx_inv_idx]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem eq_one_of_tupleEq0 {g : J0} {X : Table} (hX : Rep nPts X g)
    (h : tupleEq (apT X chainQ) chainQ = true) : g = 1 := by
  apply sep0
  intro t ht
  simp only [tupleEq, Bool.and_eq_true, beq_iff_eq] at h
  have := (allIn_eq_true.1 h.2) t (Nat.zero_le _) ht
  simp only [beq_iff_eq] at this
  rw [apT_get _ _ ht, hX _ (chainQ_lt0 ht)] at this
  exact this

@[expose] noncomputable def genG0 (z : ℤ) : J0 :=
  if z = 1 then ga0 else if z = -1 then ga0⁻¹ else if z = 2 then gb0 else gb0⁻¹

theorem rep_genT0 (z : ℤ) : Rep nPts (genT (orbitData ()) z) (genG0 z) := by
  unfold genT genG0
  split_ifs
  · exact rep_ga0
  · exact Rep.inv_of_invOK rep_ga0 facts.2.2.2.2.2.1
  · exact rep_gb0
  · exact Rep.inv_of_invOK rep_gb0 facts.2.2.2.2.2.2

@[expose] noncomputable def img0 (k : ℕ) : J0 := wordG genG0 imgWords[k]!

@[expose] noncomputable def imgG0 (z : ℤ) : J0 :=
  if 0 < z then img0 (z - 1).toNat else (img0 (-z - 1).toNat)⁻¹

theorem wordG_map_letterOf0 (v : List (ℕ × Bool)) :
    wordG imgG0 (v.map letterOf) = wordProd img0 v := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    simp only [wordProd, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b <;> simp [letterOf, imgG0]

private theorem presentation_eq0 :
    SporadicName.ONan.presentation = Sporadic.onanPresentation := rfl

end CertificateChecks.KernelSpor.ONC

end
