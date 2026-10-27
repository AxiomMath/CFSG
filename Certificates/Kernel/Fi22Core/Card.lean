module

public import Certificates.Kernel.Fi22.Final
public import Certificates.Kernel.Fi22Core.RelChecks
public import Certificates.Kernel.Fi22.Letters
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import Certificates.Kernel.Fi22Core.Conj
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Sporadic.Presentation.Common
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22C.relAll CertificateChecks.KernelFi22C.relSl 78

namespace CertificateChecks.KernelFi22C

open CFSG.KC.Enum CFSG.KS CFSG.KS.PC CFSG.KS.Fi22L CFSG.KS.TW CFSG.Sporadic.Fi22.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelCo2 CertificateChecks.KernelFi22

theorem card_closure_le (P : TauCeti.GroupPresentation) [Finite (PresentedGroup P.relatorSet)]
    {G : Type*} [Group G] [Finite G] (x : ℕ → G) (hrel : ∀ w ∈ P.relatorLetters, swd x w = 1) :
    Nat.card (Subgroup.closure (x '' {g | g < P.generatorCount})) ≤
      Nat.card (PresentedGroup P.relatorSet) := by
  have hr : ∀ r ∈ P.relatorSet, FreeGroup.lift (fun i : Fin P.generatorCount => x i.val) r = 1 := by
    intro r hr
    rw [CFSG.Sporadic.Presentation.relatorSet_eq] at hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    have := hrel (w.map fun l => (l.1.val, l.2))
      (by rw [TauCeti.GroupPresentation.relatorLetters_def]; exact List.mem_map_of_mem hw)
    unfold swd at this
    rw [List.map_map] at this
    rw [← this]
    congr 1
    apply List.map_congr_left
    rintro ⟨g, b⟩ _
    cases b <;> rfl
  let φ : PresentedGroup P.relatorSet →* G := PresentedGroup.toGroup hr
  have hle : Subgroup.closure (x '' {g | g < P.generatorCount}) ≤ φ.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨PresentedGroup.of ⟨g, hg⟩, PresentedGroup.toGroup.of hr⟩
  exact (Subgroup.card_le_of_le hle).trans (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective)

theorem actN_prod {n : Nat} (ps : List (Equiv.Perm (Fin n))) (x : Nat) :
    actN ps.prod x = ps.foldr (fun p y => actN p y) x := by
  induction ps with
  | nil => rw [List.prod_nil, actN_one, List.foldr_nil]
  | cons p ps ih => rw [List.prod_cons, actN_mul, ih, List.foldr_cons]

theorem perm_ext {n : Nat} {g h : Equiv.Perm (Fin n)} (e : ∀ x < n, actN g x = actN h x) : g = h := by
  ext x
  have := e x x.isLt
  rwa [actN_of_lt _ x.isLt, actN_of_lt _ x.isLt] at this

theorem permOfT_act {n : Nat} {t : Table} {f : Nat → Nat} (ht : TR n t f)
    (hinj : ∀ x < n, ∀ y < n, f x = f y → x = y) {x : Nat} (hx : x < n) : actN (permOfT n t) x = f x := by
  rw [actN_of_lt _ hx, permOfT_val (fun y hy => by rw [(ht.2 y hy).1]; exact (ht.2 y hy).2)
    (fun a ha b hb e => by rw [(ht.2 a ha).1, (ht.2 b hb).1] at e; exact hinj a ha b hb e)]
  exact (ht.2 x hx).1

noncomputable abbrev sA : Equiv.Perm (Fin 3510) := permOfT 3510 orbL.alpha
noncomputable abbrev sB : Equiv.Perm (Fin 3510) := permOfT 3510 orbL.beta

noncomputable abbrev xg (k : ℕ) : Equiv.Perm (Fin 3510) := if k = 0 then sA else sB

theorem gfacts {y : Nat} (hy : y < 3510) : reg ljPacked 0 y < 3510 ∧ reg ljPacked 1 y < 3510 ∧
    reg ljPacked 2 y < 3510 ∧ reg ljPacked 2 (reg ljPacked 1 y) = y ∧
      reg ljPacked 1 (reg ljPacked 2 y) = y :=
  gen_facts CertificateChecks.KernelFi22.Letters.gen_ok hy

theorem reg_lk {t : Nat} (ht : t < 2) (y : Nat) : reg ljPacked t y = lk (orbT t) y := by
  unfold reg
  rw [regT_lt ht]

theorem act_sA {y : Nat} (hy : y < 3510) : actN sA y = reg ljPacked 0 y :=
  permOfT_act (tr_alpha CertificateChecks.KernelFi22.Letters.gen_ok) (fun a ha b hb e => by
    have h1 := (tree_facts ha).2.2.1
    have h2 := (tree_facts hb).2.2.1
    simp only [reg_lk (t := 0) (by norm_num)] at e
    calc a = lk (orbT 0) (lk (orbT 0) a) := h1.symm
      _ = lk (orbT 0) (lk (orbT 0) b) := by rw [e]
      _ = b := h2) hy

theorem act_sB {y : Nat} (hy : y < 3510) : actN sB y = reg ljPacked 1 y :=
  permOfT_act (tr_beta CertificateChecks.KernelFi22.Letters.gen_ok) (fun a ha b hb e => by
    rw [← (gfacts ha).2.2.2.1, ← (gfacts hb).2.2.2.1, e]) hy

theorem actN_inv_of {n : Nat} (g : Equiv.Perm (Fin n)) {x y : Nat} (h : actN g x = y) :
    actN g⁻¹ y = x := by
  rw [← h, ← actN_mul, inv_mul_cancel, actN_one]

theorem act_sAi {y : Nat} (hy : y < 3510) : actN sA⁻¹ y = reg ljPacked 0 y := by
  apply actN_inv_of sA
  rw [act_sA (gfacts hy).1, reg_lk (by norm_num), reg_lk (by norm_num)]
  exact (tree_facts hy).2.2.1

theorem act_sBi {y : Nat} (hy : y < 3510) : actN sB⁻¹ y = reg ljPacked 2 y := by
  apply actN_inv_of sB
  rw [act_sB (gfacts hy).2.2.1]
  exact (gfacts hy).2.2.2.2

theorem appL_act (l : ℕ × Bool) {y : Nat} (hy : y < 3510) :
    actN (if l.2 then xg l.1 else (xg l.1)⁻¹) y = appL l y ∧ appL l y < 3510 := by
  obtain ⟨g, b⟩ := l
  have hf := gfacts hy
  unfold appL xg
  by_cases hg : g = 0
  · subst hg
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by rw [act_sAi hy, reg_lk (by norm_num)]; rfl, by rw [← reg_lk (t := 0) (by norm_num)]; exact hf.1⟩
    · simp only [↓reduceIte]
      refine ⟨by rw [act_sA hy, reg_lk (by norm_num)]; rfl, by rw [← reg_lk (t := 0) (by norm_num)]; exact hf.1⟩
  · have e : Nat.beq g 0 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact hg (Nat.eq_of_beq_eq_true e)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, hg]
      refine ⟨by rw [act_sBi hy]; simp only [e], by simp only [e]; exact hf.2.2.1⟩
    · simp only [↓reduceIte, hg]
      refine ⟨by rw [act_sB hy, reg_lk (by norm_num)]; simp only [e], by
        simp only [e]; rw [← reg_lk (t := 1) (by norm_num)]; exact hf.2.1⟩

theorem word_act (w : List (ℕ × Bool)) {y : Nat} (hy : y < 3510) :
    w.foldr (fun l z => actN (if l.2 then xg l.1 else (xg l.1)⁻¹) z) y = wordAt w y ∧ wordAt w y < 3510 := by
  induction w with
  | nil => exact ⟨rfl, hy⟩
  | cons l w ih =>
    rw [List.foldr_cons, ih.1]
    change _ = strictN (wordAt w y) (fun y => appL l y) ∧ strictN (wordAt w y) (fun y => appL l y) < 3510
    rw [Raw.Orb.strictN_eq]
    exact appL_act l ih.2

theorem rel_fix {r : Nat} (hr : r < 13) {y : Nat} (hy : y < 3510) :
    wordAt (List.getD CFSG.KD.OrdFi22.rels r []) y = y := by
  have hs : 6 * r + y / 585 < 78 := by omega
  have h := relAll (6 * r + y / 585) hs
  unfold relSl at h
  have e1 : Nat.div (6 * r + y / 585) 6 = r := by
    change (6 * r + y / 585) / 6 = r
    omega
  have e2 : Nat.mul (Nat.mod (6 * r + y / 585) 6) 585 = y / 585 * 585 := by
    change (6 * r + y / 585) % 6 * 585 = y / 585 * 585
    congr 1
    omega
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, e1, e2] at h
  have h' := allN_spec h (y % 585) (Nat.mod_lt _ (by norm_num))
  have e3 : Nat.add (y / 585 * 585) (y % 585) = y := by
    change y / 585 * 585 + y % 585 = y
    omega
  rw [e3] at h'
  unfold relAt at h'
  exact Nat.eq_of_beq_eq_true h'

theorem rels_hold : ∀ w ∈ P.relatorLetters, swd xg w = 1 := by
  intro w hw
  rw [CFSG.KD.OrdFi22.rels_eq] at hw
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 hw
  have hlen : CFSG.KD.OrdFi22.rels.length = 13 := rfl
  have hr' : r < 13 := by rw [← hlen]; exact hr
  apply perm_ext
  intro y hy
  unfold swd
  rw [actN_prod, List.foldr_map, actN_one, (word_act _ hy).1]
  have := rel_fix hr' hy
  rwa [List.getD_eq_getElem _ _ hr] at this

noncomputable abbrev HG : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure (xg '' {g | g < P.generatorCount})

theorem xg_zero : xg 0 = sA := by simp [xg]
theorem xg_one : xg 1 = sB := by simp [xg]

theorem sA_mem : sA ∈ HG := by
  rw [← xg_zero]
  refine Subgroup.subset_closure ⟨0, ?_, rfl⟩
  change 0 < P.generatorCount
  rw [gens_eq]
  norm_num

theorem sB_mem : sB ∈ HG := by
  rw [← xg_one]
  refine Subgroup.subset_closure ⟨1, ?_, rfl⟩
  change 1 < P.generatorCount
  rw [gens_eq]
  norm_num

theorem TR_act {n : Nat} {t : Table} {f : Nat → Nat} {σ : Equiv.Perm (Fin n)} (ht : TR n t f)
    (h : ∀ x < n, f x = actN σ x) : TR n t (actN σ) := TR_congr ht h

theorem gen_mem (z : Int) : ∃ σ ∈ HG, TR 3510 (genTables orbL z) (actN σ) := by
  have hg := CertificateChecks.KernelFi22.Letters.gen_ok
  unfold genTables
  by_cases h1 : z = 1 ∨ z = -1
  · simp only [h1, ↓reduceIte]
    exact ⟨sA, sA_mem, TR_act (tr_alpha hg) fun x hx => (act_sA hx).symm⟩
  by_cases h2 : z = 2
  · simp only [h2, ↓reduceIte]
    exact ⟨sB, sB_mem, TR_act (tr_beta hg) fun x hx => (act_sB hx).symm⟩
  · simp only [h1, h2, ↓reduceIte]
    exact ⟨sB⁻¹, Subgroup.inv_mem _ sB_mem, TR_act (tr_binv hg) fun x hx => (act_sBi hx).symm⟩

noncomputable def gperm (z : Int) : Equiv.Perm (Fin 3510) := (gen_mem z).choose

theorem word_mem (w : List Int) :
    TR 3510 (wordT 3510 (genTables orbL) w) (actN (w.map gperm).prod) ∧ (w.map gperm).prod ∈ HG := by
  have hT := wordT_TR (n := 3510) (by norm_num) (gens := genTables orbL)
    (G := fun z => actN (gperm z)) w fun z _ => (gen_mem z).choose_spec.2
  refine ⟨TR_congr hT fun x _ => ?_, list_prod_mem fun σ hσ => ?_⟩
  · rw [actN_prod, List.foldr_map]
  · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hσ
    exact (gen_mem z).choose_spec.1

theorem perm_of_TR {t : Table} {σ : Equiv.Perm (Fin 3510)} (ht : TR 3510 t (actN σ)) :
    permOfT 3510 t = σ :=
  perm_ext fun x hx => permOfT_act ht (fun a ha b hb e => by
    rw [actN_of_lt _ ha, actN_of_lt _ hb] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e))) hx

theorem letter_mem {l : Nat} (hl : l < 32) : permOfT 3510 (chainLetters orbL)[l]! ∈ HG := by
  have hsz := CertificateChecks.KernelFi22.Letters.letters.1
  have hl' : l < (chainLetters orbL).size := by rw [hsz]; exact hl
  have e : chainLetters orbL = buildLetters 3510 (genTables orbL) (chainWords ()) := rfl
  have hget : (chainLetters orbL)[l]! =
      if l % 2 = 0 then wordT 3510 (genTables orbL) (chainWords ())[l / 2]!
      else invT 3510 (wordT 3510 (genTables orbL) (chainWords ())[l / 2]!) := by
    rw [getElem!_pos _ l hl']
    simp only [e, buildLetters, Array.getElem_ofFn]
  obtain ⟨hT, hm⟩ := word_mem (chainWords ())[l / 2]!
  generalize ((chainWords ())[l / 2]!.map gperm).prod = σ at hT hm
  rw [hget]
  split_ifs
  · rw [perm_of_TR hT]
    exact hm
  · have hI := invT_TR (n := 3510) (by norm_num) hT (g := actN σ⁻¹) fun i hi =>
      ⟨actN_lt _ hi, by rw [← actN_mul, mul_inv_cancel, actN_one],
        by rw [← actN_mul, inv_mul_cancel, actN_one]⟩
    rw [perm_of_TR hI]
    exact Subgroup.inv_mem _ hm

theorem letters_card :
    Nat.card (Subgroup.closure (Set.range fun l : Fin 32 => permOfT 3510 (chainLetters orbL)[l.val]!)) ≤
      64561751654400 := by
  have hfin : Finite (PresentedGroup P.relatorSet) := fi22_bound.1
  have hle : Subgroup.closure (Set.range fun l : Fin 32 => permOfT 3510 (chainLetters orbL)[l.val]!) ≤
      HG := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    exact letter_mem l.isLt
  exact (Subgroup.card_le_of_le hle).trans ((card_closure_le P xg rels_hold).trans fi22_bound.2)

end CertificateChecks.KernelFi22C

end
