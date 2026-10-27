
module

public import Certificates.Kernel.Sporadic.SuzK.Card
public import Certificates.Kernel.Sporadic.SuzK.Letters
public import CFSG.Certificates.Kernel.Spor.PChainSound

public section

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.Sporadic.Bridge CFSG.KS.PC CFSG.KS.TW CFSG.Sporadic.Suz.Native CFSG.Sporadic.Th.Native
  CFSG.F3.Native CFSG.Perm.Native CFSG.KS.PEnum

@[expose] def Realizes (g : M64ˣ) (π : Equiv.Perm (Fin 22880)) : Prop :=
  ∀ k : Fin 22880, (g : M64) * KM k.val * ((g⁻¹ : M64ˣ) : M64) = KM (π k).val

theorem alpha_inj : ∀ x < 22880, ∀ y < 22880, ap orbLit.alpha x = ap orbLit.alpha y → x = y := by
  intro x hx y hy e
  rw [alpha_ap hx, alpha_ap hy] at e
  rw [← alpha_inv hx, ← alpha_inv hy, e]

theorem beta_inj : ∀ x < 22880, ∀ y < 22880, ap orbLit.beta x = ap orbLit.beta y → x = y := by
  intro x hx y hy e
  rw [beta_ap hx, beta_ap hy] at e
  rw [← beta_ord hx, ← beta_ord hy, e]

@[expose] noncomputable def sA : Equiv.Perm (Fin 22880) := permOfT 22880 orbLit.alpha

@[expose] noncomputable def sB : Equiv.Perm (Fin 22880) := permOfT 22880 orbLit.beta

theorem alpha_rng : ∀ y < 22880, ap orbLit.alpha y < 22880 := fun y hy => by
  rw [alpha_ap hy]
  exact al_lt hy

theorem beta_rng : ∀ y < 22880, ap orbLit.beta y < 22880 := fun y hy => by
  rw [beta_ap hy]
  exact be_lt hy

theorem sA_eq : sA = permOfT 22880 orbLit.alpha := by
  unfold sA
  rfl

theorem sB_eq : sB = permOfT 22880 orbLit.beta := by
  unfold sB
  rfl

theorem sA_val (x : Fin 22880) : (sA x : Nat) = r32 AL x := by
  rw [sA_eq, permOfT_val alpha_rng alpha_inj x]
  exact alpha_ap x.isLt

theorem sB_val (x : Fin 22880) : (sB x : Nat) = r32 BE x := by
  rw [sB_eq, permOfT_val beta_rng beta_inj x]
  exact beta_ap x.isLt

theorem real_uA : Realizes uA sA := by
  intro k
  rw [sA_val, uA_val, uA_inv_val]
  exact conjA_mat k.isLt

theorem real_uB : Realizes uB sB := by
  intro k
  rw [sB_val, uB_val, uB_inv_val]
  exact conjB_mat k.isLt

theorem real_one : Realizes 1 1 := by
  intro k
  rw [inv_one, Units.val_one, one_mul, mul_one, Equiv.Perm.one_apply]

theorem real_mul {g h : M64ˣ} {π σ : Equiv.Perm (Fin 22880)} (hg : Realizes g π) (hh : Realizes h σ) :
    Realizes (g * h) (π * σ) := by
  intro k
  rw [mul_inv_rev, Units.val_mul, Units.val_mul, Equiv.Perm.mul_apply, ← hg (σ k), ← hh k]
  simp only [mul_assoc]

theorem real_inv {g : M64ˣ} {π : Equiv.Perm (Fin 22880)} (hg : Realizes g π) : Realizes g⁻¹ π⁻¹ := by
  intro k
  have h := hg (π⁻¹ k)
  have hk : π (π⁻¹ k) = k := by simp
  rw [hk] at h
  rw [← h, inv_inv]
  have e1 : ((g⁻¹ : M64ˣ) : M64) * (g : M64) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((g⁻¹ : M64ˣ) : M64) * ((g : M64) * KM (π⁻¹ k).val * ((g⁻¹ : M64ˣ) : M64)) * (g : M64) =
      (((g⁻¹ : M64ˣ) : M64) * (g : M64)) * KM (π⁻¹ k).val * (((g⁻¹ : M64ˣ) : M64) * (g : M64)) := by
        simp only [mul_assoc]
    _ = KM (π⁻¹ k).val := by rw [e1, one_mul, mul_one]

theorem real_unique {g : M64ˣ} {π σ : Equiv.Perm (Fin 22880)} (hπ : Realizes g π) (hσ : Realizes g σ) :
    π = σ := by
  apply Equiv.ext
  intro k
  apply Fin.ext
  exact KM_inj (π k).isLt (σ k).isLt ((hπ k).symm.trans (hσ k))

theorem exists_real : ∀ g ∈ H, ∃ π, Realizes g π := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨sA, real_uA⟩
    · exact ⟨sB, real_uB⟩
  | one => exact ⟨1, real_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨π, hπ⟩ := hx
    obtain ⟨σ, hσ⟩ := hy
    exact ⟨π * σ, real_mul hπ hσ⟩
  | inv x _ hx =>
    obtain ⟨π, hπ⟩ := hx
    exact ⟨π⁻¹, real_inv hπ⟩

@[expose] noncomputable def piOf (g : H) : Equiv.Perm (Fin 22880) := (exists_real g.1 g.2).choose

theorem piOf_spec (g : H) : Realizes g (piOf g) := (exists_real g.1 g.2).choose_spec

theorem piOf_one : piOf 1 = 1 := real_unique (piOf_spec 1) real_one

theorem piOf_mul (g h : H) : piOf (g * h) = piOf g * piOf h :=
  real_unique (piOf_spec (g * h)) (real_mul (piOf_spec g) (piOf_spec h))

@[expose] noncomputable def rho : H →* Equiv.Perm (Fin 22880) where
  toFun := piOf
  map_one' := piOf_one
  map_mul' := piOf_mul

theorem uA_H : uA ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)

theorem uB_H : uB ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sA_range : sA ∈ rho.range :=
  ⟨⟨uA, uA_H⟩, real_unique (piOf_spec ⟨uA, uA_H⟩) real_uA⟩

theorem sB_range : sB ∈ rho.range :=
  ⟨⟨uB, uB_H⟩, real_unique (piOf_spec ⟨uB, uB_H⟩) real_uB⟩

noncomputable abbrev HG : Subgroup (Equiv.Perm (Fin 22880)) := Subgroup.closure {sA, sB}

theorem card_HG : Nat.card HG ≤ 448345497600 := by
  have hle : HG ≤ rho.range := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases (Set.mem_insert_iff.1 hx) with h | h
    · rw [h]
      exact sA_range
    · rw [Set.mem_singleton_iff.1 h]
      exact sB_range
  exact (Subgroup.card_le_of_le hle).trans
    ((Nat.card_le_card_of_surjective _ rho.rangeRestrict_surjective).trans card_H)

theorem actN_prod {n : Nat} (ps : List (Equiv.Perm (Fin n))) (x : Nat) :
    actN ps.prod x = ps.foldr (fun p y => actN p y) x := by
  induction ps with
  | nil => rw [List.prod_nil, actN_one, List.foldr_nil]
  | cons p ps ih => rw [List.prod_cons, actN_mul, ih, List.foldr_cons]

theorem perm_ext {n : Nat} {g h : Equiv.Perm (Fin n)} (e : ∀ x < n, actN g x = actN h x) : g = h := by
  ext x
  have := e x x.isLt
  rwa [actN_of_lt _ x.isLt, actN_of_lt _ x.isLt] at this

theorem TR_congr' {n : Nat} {t : Table} {f g : Nat → Nat} (h : TR n t f) (hfg : ∀ i < n, f i = g i) :
    TR n t g :=
  ⟨h.1, fun i hi => by rw [← hfg i hi]; exact h.2 i hi⟩

theorem act_sA {x : Nat} (hx : x < 22880) : actN sA x = r32 AL x := by
  rw [actN_of_lt _ hx, sA_val]

theorem act_sB {x : Nat} (hx : x < 22880) : actN sB x = r32 BE x := by
  rw [actN_of_lt _ hx, sB_val]

theorem actN_inv_of {g : Equiv.Perm (Fin 22880)} {x y : Nat} (h : actN g y = x) : actN g⁻¹ x = y := by
  rw [← h, ← actN_mul, inv_mul_cancel, actN_one]

theorem act_sBi {x : Nat} (hx : x < 22880) : actN sB⁻¹ x = r32 BE (r32 BE x) :=
  actN_inv_of (by rw [act_sB (be_lt (be_lt hx)), beta_ord hx])

theorem sA_mem : sA ∈ HG := Subgroup.subset_closure (Set.mem_insert _ _)

theorem sB_mem : sB ∈ HG := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem gen_mem (z : Int) : ∃ σ ∈ HG, TR 22880 (genTables orbLit z) (actN σ) := by
  have ht := gen_TR z
  unfold gfun at ht
  unfold genTables at ht ⊢
  by_cases h1 : z = 1 ∨ z = -1
  · simp only [h1, ↓reduceIte] at ht ⊢
    exact ⟨sA, sA_mem, TR_congr' ht fun x hx => (act_sA hx).symm⟩
  by_cases h2 : z = 2
  · simp only [h1, h2, ↓reduceIte] at ht ⊢
    exact ⟨sB, sB_mem, TR_congr' ht fun x hx => (act_sB hx).symm⟩
  · simp only [h1, h2, ↓reduceIte] at ht ⊢
    exact ⟨sB⁻¹, Subgroup.inv_mem _ sB_mem, TR_congr' ht fun x hx => (act_sBi hx).symm⟩

@[expose] noncomputable def gperm (z : Int) : Equiv.Perm (Fin 22880) := (gen_mem z).choose

theorem word_mem (w : List Int) :
    TR 22880 (wordT 22880 (genTables orbLit) w) (actN (w.map gperm).prod) ∧
      (w.map gperm).prod ∈ HG := by
  have hT := wordT_TR (n := 22880) (by norm_num) (gens := genTables orbLit)
    (G := fun z => actN (gperm z)) w fun z _ => (gen_mem z).choose_spec.2
  refine ⟨TR_congr' hT fun x _ => ?_, list_prod_mem fun σ hσ => ?_⟩
  · rw [actN_prod, List.foldr_map]
  · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hσ
    exact (gen_mem z).choose_spec.1

theorem permOfT_act {t : Table} {σ : Equiv.Perm (Fin 22880)} (ht : TR 22880 t (actN σ)) :
    permOfT 22880 t = σ := by
  apply perm_ext
  intro x hx
  have hinj : ∀ a < 22880, ∀ b < 22880, ap t a = ap t b → a = b := by
    intro a ha b hb e
    rw [(ht.2 a ha).1, (ht.2 b hb).1, actN_of_lt _ ha, actN_of_lt _ hb] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e))
  have hr : ∀ y < 22880, ap t y < 22880 := fun y hy => by
    rw [(ht.2 y hy).1]
    exact (ht.2 y hy).2
  rw [actN_of_lt _ hx, permOfT_val hr hinj]
  exact (ht.2 x hx).1

theorem letter_get {j : Nat} (hj : j < 14) :
    (chainLetters orbLit)[2 * j]! = wordT 22880 (genTables orbLit) (chainWords ())[j]! ∧
      (chainLetters orbLit)[2 * j + 1]! =
        invT 22880 (wordT 22880 (genTables orbLit) (chainWords ())[j]!) := by
  have hws := words_data.1
  have d0 : 2 * j / 2 = j := by omega
  have m0 : 2 * j % 2 = 0 := by omega
  have d1 : (2 * j + 1) / 2 = j := by omega
  have m1 : (2 * j + 1) % 2 = 1 := by omega
  rw [chainLetters_eq]
  unfold buildLetters
  constructor
  · rw [getElem!_pos _ _ (by rw [Array.size_ofFn, hws]; omega), Array.getElem_ofFn]
    simp only [d0, m0, ite_true]
  · rw [getElem!_pos _ _ (by rw [Array.size_ofFn, hws]; omega), Array.getElem_ofFn]
    simp only [d1, m1, Nat.one_ne_zero, ite_false]

theorem letter_mem {l : Nat} (hl : l < 28) : permOfT 22880 (chainLetters orbLit)[l]! ∈ HG := by
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · obtain ⟨hT, hm⟩ := word_mem (chainWords ())[j]!
    rw [(letter_get (by omega)).1, permOfT_act hT]
    exact hm
  · obtain ⟨hT, hm⟩ := word_mem (chainWords ())[j]!
    generalize ((chainWords ())[j]!.map gperm).prod = σ at hT hm
    have hI := invT_TR (n := 22880) (by norm_num) hT (g := actN σ⁻¹) fun i hi =>
      ⟨actN_lt _ hi, by rw [← actN_mul, mul_inv_cancel, actN_one],
        by rw [← actN_mul, inv_mul_cancel, actN_one]⟩
    rw [(letter_get (by omega)).2, permOfT_act hI]
    exact Subgroup.inv_mem _ hm

theorem letters_card :
    Nat.card (Subgroup.closure (Set.range fun l : Fin 28 =>
      permOfT 22880 (chainLetters orbLit)[l.val]!)) ≤ 448345497600 := by
  have hle : Subgroup.closure (Set.range fun l : Fin 28 =>
      permOfT 22880 (chainLetters orbLit)[l.val]!) ≤ HG := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    exact letter_mem l.isLt
  exact (Subgroup.card_le_of_le hle).trans card_HG

end CertificateChecks.KernelSpor.SuzK

end
