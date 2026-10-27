module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Beta4
public import Certificates.Kernel.M23Aut.Checks
public import Certificates.Kernel.M23Aut.ChecksG
public import CFSG.Certificates.Kernel.M23AutKSound

public section

namespace CFSG.KD.M23Aut

open Equiv MulAction CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Asc94 CFSG.M23Pair
  CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.M23Aut CFSG.Sporadic.Schreier
open scoped Pointwise

theorem hn23 : (23 : ℕ) ≤ 32 := by norm_num

theorem img_iff (σ : Perm (Fin 23)) (p q : Fin 23) : img (code σ) p.val = q.val ↔ σ p = q := by
  rw [img_code hn23, Fin.val_inj]

theorem pairK_code (σ : Perm (Fin 23)) (a b : Fin 23) :
    pairK (code σ) a.val b.val = true ↔ (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a) := by
  rw [pairK_iff, img_iff, img_iff, img_iff, img_iff]

theorem fixK_code3 (σ : Perm (Fin 23)) (a b c : Fin 23) :
    fixK (code σ) [a.val, b.val, c.val] = true ↔ σ a = a ∧ σ b = b ∧ σ c = c := by
  simp only [fixK_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    img_iff]

theorem fixK_code4 (σ : Perm (Fin 23)) (a b c d : Fin 23) :
    fixK (code σ) [a.val, b.val, c.val, d.val] = true ↔ σ a = a ∧ σ b = b ∧ σ c = c ∧ σ d = d := by
  simp only [fixK_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    img_iff]

theorem hep_mem : ∀ x : Fin 23, x ∈ heptad₀ ↔ x.val ∈ ([5, 7, 9, 16, 19, 21, 22] : List ℕ) := by
  decide

theorem hep_lt : ∀ p ∈ ([5, 7, 9, 16, 19, 21, 22] : List ℕ), p < 23 := by decide

theorem setK_hep (σ : Perm (Fin 23)) :
    setK (code σ) [5, 7, 9, 16, 19, 21, 22] = true ↔ ∀ x ∈ heptad₀, σ x ∈ heptad₀ := by
  rw [setK_iff]
  constructor
  · intro h x hx
    rw [hep_mem] at hx ⊢
    rw [← img_code hn23]
    exact h _ hx
  · intro h p hp
    have hx : (⟨p, hep_lt p hp⟩ : Fin 23) ∈ heptad₀ := (hep_mem _).2 hp
    have := (hep_mem _).1 (h _ hx)
    rw [← img_code hn23] at this
    exact this

theorem mem_M2bar_iff' (g : ↥NativeSporadic.M23) :
    g ∈ M2bar ↔ ∀ x ∈ heptad₀, (g : Perm (Fin 23)) x ∈ heptad₀ := by
  constructor
  · intro hg x hx
    exact (CFSG.QuasithinUnique.Vol2Native.L239.stab_mem_iff.1 hg x).2 hx
  · intro h
    rw [mem_stabilizer_iff]
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_smul_finset])
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
    exact h x hx

abbrev HB : Subgroup ↥NativeSporadic.M23 := Gbar ⊓ M2bar

abbrev IxS : Subgroup ↥NativeSporadic.M23 :=
  stabilizer ↥NativeSporadic.M23 (pair (16 : Fin 23) 19 (by decide)) ⊓ Gbar

abbrev F4S : Subgroup ↥NativeSporadic.M23 :=
  fixingSubgroup ↥NativeSporadic.M23 (({16, 19, 21, 22} : Finset (Fin 23)) : Set (Fin 23))

theorem inHbarK_iff (g : ↥NativeSporadic.M23) :
    inHbarK (code (g : Perm (Fin 23))) = true ↔ g ∈ HB := by
  change andB (setK (code (g : Perm (Fin 23))) [5, 7, 9, 16, 19, 21, 22])
    (pairK (code (g : Perm (Fin 23))) (21 : Fin 23).val (22 : Fin 23).val) = true ↔ _
  rw [andB_iff, setK_hep, pairK_code, Subgroup.mem_inf, mem_Gbar_iff, mem_M2bar_iff']
  exact and_comm

theorem inPbarK_iff (g : ↥NativeSporadic.M23) :
    inPbarK (code (g : Perm (Fin 23))) = true ↔ g ∈ Lbar ∧ g ∈ M2bar := by
  change andB (fixK (code (g : Perm (Fin 23)))
      [(19 : Fin 23).val, (21 : Fin 23).val, (22 : Fin 23).val])
    (setK (code (g : Perm (Fin 23))) [5, 7, 9, 16, 19, 21, 22]) = true ↔ _
  rw [andB_iff, fixK_code3, setK_hep, mem_Lbar_iff, mem_M2bar_iff']

theorem inIxK_iff (g : ↥NativeSporadic.M23) :
    inIxK (code (g : Perm (Fin 23))) = true ↔ g ∈ IxS := by
  change andB (pairK (code (g : Perm (Fin 23))) (16 : Fin 23).val (19 : Fin 23).val)
    (pairK (code (g : Perm (Fin 23))) (21 : Fin 23).val (22 : Fin 23).val) = true ↔ _
  rw [andB_iff, pairK_code, pairK_code, Subgroup.mem_inf, mem_Gbar_iff, mem_stabilizer_iff,
    smul_pair, pair_eq_iff, m23_smul_eq, m23_smul_eq]

theorem inF4K_iff (g : ↥NativeSporadic.M23) :
    inF4K (code (g : Perm (Fin 23))) = true ↔ g ∈ F4S := by
  change fixK (code (g : Perm (Fin 23)))
    [(16 : Fin 23).val, (19 : Fin 23).val, (21 : Fin 23).val, (22 : Fin 23).val] = true ↔ _
  rw [fixK_code4, mem_fixingSubgroup_iff]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, m23_smul_eq]

theorem fixL_iff (g : ↥NativeSporadic.M23) :
    fixK (code (g : Perm (Fin 23))) [19, 21, 22] = true ↔ g ∈ Lbar := by
  change fixK (code (g : Perm (Fin 23)))
    [(19 : Fin 23).val, (21 : Fin 23).val, (22 : Fin 23).val] = true ↔ _
  rw [fixK_code3, mem_Lbar_iff]

theorem F4S_le : F4S ≤ Lbar := by
  intro g hg
  rw [mem_fixingSubgroup_iff] at hg
  rw [mem_Lbar_iff]
  exact ⟨hg 19 (by simp), hg 21 (by simp), hg 22 (by simp)⟩

theorem mem_IxS_of_mem {g : ↥NativeSporadic.M23}
    (hg : g ∈ quadStab ↥NativeSporadic.M23 (16 : Fin 23) 19 21 22 ⊓ Gbar) : g ∈ IxS := by
  obtain ⟨hq, hG⟩ := Subgroup.mem_inf.mp hg
  have hset : ∀ x : Fin 23, x ∈ ({16, 19, 21, 22} : Set (Fin 23)) →
      (g : Equiv.Perm (Fin 23)) x ∈ ({16, 19, 21, 22} : Set (Fin 23)) := by
    intro x hx
    rw [← mem_stabilizer_iff.mp hq]
    exact Set.smul_mem_smul_set hx
  have hinj := (g : Equiv.Perm (Fin 23)).injective
  have h16 := hset 16 (by simp)
  have h19 := hset 19 (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h16 h19
  refine Subgroup.mem_inf.mpr ⟨?_, hG⟩
  rw [mem_stabilizer_iff, smul_pair, pair_eq_iff, m23_smul_eq, m23_smul_eq]
  rcases mem_Gbar_iff.mp hG with ⟨h21, h22⟩ | ⟨h21, h22⟩ <;>
    rcases h16 with h16 | h16 | h16 | h16 <;> rcases h19 with h19 | h19 | h19 | h19 <;>
      first
        | exact Or.inl ⟨h16, h19⟩
        | exact Or.inr ⟨h16, h19⟩
        | exact absurd (hinj (h16.trans h19.symm)) (by decide)
        | exact absurd (hinj (h16.trans h21.symm)) (by decide)
        | exact absurd (hinj (h16.trans h22.symm)) (by decide)
        | exact absurd (hinj (h19.trans h21.symm)) (by decide)
        | exact absurd (hinj (h19.trans h22.symm)) (by decide)

abbrev wI {X : Type*} [Group X] (S : List X) : List X := S ++ S.map (·⁻¹)

theorem map_wI {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) (S : List X) :
    (wI S).map φ = wI (S.map φ) := by
  simp only [wI, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun g _ => map_inv φ g

theorem prodW_hom {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) (S : List X) (w : List ℕ) :
    φ (prodW (wI S) w) = prodW (wI (S.map φ)) w := by
  rw [map_prodW, map_wI]

theorem conj_pow' {X : Type*} [Group X] (c z : X) (k : ℕ) :
    (c * z * c⁻¹) ^ k = c * z ^ k * c⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

theorem e_eq : e = one 23 := beq_iff.1 (andB_iff.1 ch7108_ab).1

theorem evK_w {X : Type*} [Group X] (φ : X →* Perm (Fin 23)) (S : List X) (w : List ℕ)
    (hw : ∀ l ∈ w, l < 2 * S.length) :
    evK 23 e (withInv 23 (S.map fun g => code (φ g))) w = code (φ (prodW (wI S) w)) := by
  rw [e_eq, withInv_hom φ hn23, evK_hom φ hn23]
  intro l hl
  have := hw l hl
  simp only [List.length_append, List.length_map]
  omega

noncomputable abbrev ιM : ↥NativeSporadic.M23 →* Perm (Fin 23) := NativeSporadic.M23.subtype

theorem tabA_eq : ∀ i : Fin 23, nth tabA i = ((m23PermA i : Fin 23) : ℕ) := by decide +kernel

theorem tabB_eq : ∀ i : Fin 23, nth tabB i = ((m23PermB i : Fin 23) : ℕ) := by decide +kernel

theorem ta_eq : ta = code (ιM m23GenA) := by
  rw [beq_iff.1 (andB_iff.1 (andB_iff.1 ch7108_ab).2).1, ofFn_eq, code_eq]
  exact E_congr fun i hi => (tabA_eq ⟨i, hi⟩).trans (vals_fin (ιM m23GenA) ⟨i, hi⟩).symm

theorem tb_eq : tb = code (ιM m23GenB) := by
  rw [beq_iff.1 (andB_iff.1 (andB_iff.1 ch7108_ab).2).2, ofFn_eq, code_eq]
  exact E_congr fun i hi => (tabB_eq ⟨i, hi⟩).trans (vals_fin (ιM m23GenB) ⟨i, hi⟩).symm

theorem ab_eq : [ta, tb] = [m23GenA, m23GenB].map fun g => code (ιM g) := by
  rw [ta_eq, tb_eq]
  rfl

noncomputable def ksM : List ↥NativeSporadic.M23 := ksW.map (prodW (wI [m23GenA, m23GenB]))

theorem ksM_length : ksM.length = 4 := by
  rw [ksM, List.length_map]
  rfl

theorem ksW_lt : ∀ w ∈ ksW, ∀ l ∈ w, l < 4 := by decide

theorem pW_lt : ∀ w ∈ pW, ∀ l ∈ w, l < 4 := by decide

theorem iW_lt : ∀ w ∈ iW, ∀ l ∈ w, l < 4 := by decide

theorem lWW_lt : ∀ l ∈ lWW, l < 4 := by decide

theorem lt_two {X : Type*} (a b : X) {l : ℕ} (h : l < 4) : l < 2 * [a, b].length := by
  simpa using h

theorem ks_eq : ks = ksM.map fun g => code (ιM g) := by
  rw [eqLK_eq ch7108_ks, ab_eq, ksM, List.map_map]
  refine List.map_congr_left fun w hw => ?_
  rw [Function.comp_apply]
  exact evK_w ιM [m23GenA, m23GenB] w fun l hl => lt_two _ _ (ksW_lt w hw l hl)

noncomputable def hAM : ↥NativeSporadic.M23 := prodW (wI ksM) [4, 3, 4, 2, 0, 1, 4, 2, 0]

noncomputable def hBM : ↥NativeSporadic.M23 := prodW (wI ksM) [2, 1, 2, 4, 2, 0]

noncomputable def fAM : ↥NativeSporadic.M23 := prodW (wI ksM) [1, 4, 2, 0, 1, 4, 2, 0]

noncomputable def fBM : ↥NativeSporadic.M23 := prodW (wI ksM) [1, 0, 2, 1, 2, 1, 4, 1]

noncomputable def fCM : ↥NativeSporadic.M23 := prodW (wI ksM) [4, 1, 2, 4, 3, 2, 1, 3, 4]

noncomputable def lWM : ↥NativeSporadic.M23 := prodW (wI [m23GenA, m23GenB]) lWW

noncomputable def lXM : ↥NativeSporadic.M23 := lWM * prodW (wI ksM) [3, 0] * lWM⁻¹

theorem evK_ks (w : List ℕ) (hw : ∀ l ∈ w, l < 8) :
    evK 23 e (withInv 23 ks) w = code (ιM (prodW (wI ksM) w)) := by
  rw [ks_eq]
  exact evK_w ιM ksM w (by rw [ksM_length]; exact hw)

theorem gens_eq : hA = code (ιM hAM) ∧ hB = code (ιM hBM) ∧ fA = code (ιM fAM) ∧
    fB = code (ιM fBM) ∧ fC = code (ιM fCM) := by
  have h := eqLK_eq ch7108_gens.1
  have ht : genW.take 5 = [[4, 3, 4, 2, 0, 1, 4, 2, 0], [2, 1, 2, 4, 2, 0],
      [1, 4, 2, 0, 1, 4, 2, 0], [1, 0, 2, 1, 2, 1, 4, 1], [4, 1, 2, 4, 3, 2, 1, 3, 4]] := rfl
  rw [ht] at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  exact ⟨h.1.trans (evK_ks _ (by decide)), h.2.1.trans (evK_ks _ (by decide)),
    h.2.2.1.trans (evK_ks _ (by decide)), h.2.2.2.1.trans (evK_ks _ (by decide)),
    h.2.2.2.2.trans (evK_ks _ (by decide))⟩

theorem lW_eq : lW = code (ιM lWM) := by
  rw [beq_iff.1 (andB_iff.1 ch7108_gens.2).1, ab_eq,
    evK_w ιM _ _ fun l hl => lt_two _ _ (lWW_lt l hl)]
  rfl

theorem lX_eq : lX = code (ιM lXM) := by
  rw [beq_iff.1 (andB_iff.1 ch7108_gens.2).2, lW_eq, evK_ks _ (by decide), code_mul hn23,
    code_inv hn23, code_mul hn23, lXM, map_mul, map_mul, map_inv]

theorem facts : inHbarK hA = true ∧ inHbarK hB = true ∧ ord8K 23 e hA = true ∧
    ord2K 23 e hB = true ∧ ord5K 23 e (mul 23 hA hB) = true ∧
    pwK 23 e (withInv 23 [hA, hB]) pW = true ∧ allL (iWT.map Prod.snd) inIxK = true ∧
    inF4K fA = true ∧ inF4K fB = true ∧ inF4K fC = true ∧ fixK lX [19, 21, 22] = true ∧
    ord3K 23 e lX = true := by
  have h := ch7108_mem
  simp only [andB_iff] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4, h5⟩, h6, h7, ⟨h8, h9, h10⟩, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem ιM_apply (g : ↥NativeSporadic.M23) : ιM g = (g : Perm (Fin 23)) := rfl

theorem hA_mem : hAM ∈ HB := by
  have h := facts.1
  rw [gens_eq.1, ιM_apply] at h
  exact (inHbarK_iff hAM).1 h

theorem hB_mem : hBM ∈ HB := by
  have h := facts.2.1
  rw [gens_eq.2.1, ιM_apply] at h
  exact (inHbarK_iff hBM).1 h

theorem fA_mem : fAM ∈ F4S := by
  have h := facts.2.2.2.2.2.2.2.1
  rw [gens_eq.2.2.1, ιM_apply] at h
  exact (inF4K_iff fAM).1 h

theorem fB_mem : fBM ∈ F4S := by
  have h := facts.2.2.2.2.2.2.2.2.1
  rw [gens_eq.2.2.2.1, ιM_apply] at h
  exact (inF4K_iff fBM).1 h

theorem fC_mem : fCM ∈ F4S := by
  have h := facts.2.2.2.2.2.2.2.2.2.1
  rw [gens_eq.2.2.2.2, ιM_apply] at h
  exact (inF4K_iff fCM).1 h

theorem lX_mem : lXM ∈ Lbar := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.1
  rw [lX_eq, ιM_apply] at h
  exact (fixL_iff lXM).1 h

noncomputable abbrev ιH : ↥HB →* Perm (Fin 23) := ιM.comp HB.subtype

theorem ιH_inj : Function.Injective ιH := fun _ _ h => Subtype.ext (Subtype.ext h)

noncomputable abbrev a' : ↥HB := ⟨hAM, hA_mem⟩

noncomputable abbrev b' : ↥HB := ⟨hBM, hB_mem⟩

theorem ιH_apply (z : ↥HB) : ιH z = ιM (z : ↥NativeSporadic.M23) := rfl

theorem a'_val : (a' : ↥NativeSporadic.M23) = hAM := rfl

theorem b'_val : (b' : ↥NativeSporadic.M23) = hBM := rfl

theorem hA_H : hA = code (ιH a') := by rw [gens_eq.1, ιH_apply, a'_val]

theorem hB_H : hB = code (ιH b') := by rw [gens_eq.2.1, ιH_apply, b'_val]

theorem hAB_codes : [hA, hB] = [a', b'].map fun g => code (ιH g) := by
  rw [hA_H, hB_H, List.map_cons, List.map_cons, List.map_nil]

theorem htree : (∀ i < hN, ∃ g ∈ Subgroup.closure {x | x ∈ [a', b']}, code (ιH g) = tC 23 hT i) ∧
    ∀ i j, i < j → j < hN → tC 23 hT i < tC 23 hT j := by
  refine treeK_sound ιH hn23 (PP := hP) (PD := hD) ?_
    fun i hi => blt_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 ch7108_gidx.1 i hi)
  rw [← hAB_codes, ← e_eq]
  exact ch7108_htree

theorem hall_H (hcard : Nat.card ↥HB ≤ 1920) (y : ↥HB) :
    ∃ j < hN, code (ιH y) = tC 23 hT j :=
  listed_all ιH (fun i hi => (htree.1 i hi).elim fun g hg => ⟨g, hg.2⟩) htree.2
    (by rw [ch7108_sizes.1]; exact hcard) y

noncomputable def gsI : List ↥HB := iW.map (prodW (wI [a', b']))

theorem iWT_snd : iWT.map Prod.snd = gsI.map fun g => code (ιH g) := by
  rw [iWT, gsI, List.map_map, List.map_map]
  refine List.map_congr_left fun w hw => ?_
  rw [Function.comp_apply, Function.comp_apply, hAB_codes]
  exact evK_w ιH [a', b'] w fun l hl => lt_two _ _ (iW_lt w hw l hl)

theorem itree : (∀ i < iN, ∃ g ∈ Subgroup.closure {x | x ∈ gsI}, code (ιH g) = tC 23 iT i) ∧
    ∀ i j, i < j → j < iN → tC 23 iT i < tC 23 iT j := by
  refine treeK_sound ιH hn23 (PP := iP) (PD := iD) ?_
    fun i hi => blt_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 ch7108_gidx.2.1 i hi)
  rw [← iWT_snd, ← e_eq]
  exact ch7108_itree

theorem closure_I_le : Subgroup.closure {x | x ∈ gsI} ≤ IxS.comap HB.subtype := by
  rw [Subgroup.closure_le]
  intro g hg
  have h := (allL_iff _ _).1 facts.2.2.2.2.2.2.1
  rw [iWT_snd] at h
  exact (inIxK_iff _).1 (h _ (List.mem_map_of_mem hg))

theorem mem_closure_I (hcard : Nat.card ↥HB ≤ 1920) (y : ↥HB) (hy : (y : ↥NativeSporadic.M23) ∈ IxS) :
    y ∈ Subgroup.closure {x | x ∈ gsI} := by
  classical
  choose! g hgcl hgc using itree.1
  choose! J hJ hJc using fun i => hall_H hcard (g i)
  set S := (Finset.range hN).filter fun j => inIxK (tC 23 hT j) = true with hS
  have hScard : S.card = 192 := by
    have h := cntN_eq hN (fun i => inIxK (tC 23 hT i))
    rw [ch7108_ix] at h
    exact h.symm
  have hTS : (Finset.range iN).image J ⊆ S := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    have hi' := Finset.mem_range.1 hi
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (hJ i), ?_⟩
    rw [← hJc i]
    exact (inIxK_iff _).2 (closure_I_le (hgcl i hi'))
  have hinj : Set.InjOn J (Finset.range iN) := by
    intro i hi i' hi' h
    have hi1 := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hi2 := Finset.mem_range.1 (Finset.mem_coe.1 hi')
    have e1 : tC 23 iT i = tC 23 iT i' := by
      rw [← hgc i hi1, ← hgc i' hi2, hJc i, hJc i', h]
    exact tC_inj itree.2 hi1 hi2 e1
  have hT : (Finset.range iN).image J = S := by
    refine Finset.eq_of_subset_of_card_le hTS ?_
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, hScard, ch7108_sizes.2.1]
  obtain ⟨j, hj, hyj⟩ := hall_H hcard y
  have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, by rw [← hyj]; exact (inIxK_iff _).2 hy⟩
  rw [← hT] at hjS
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.1 hjS
  have hyg : y = g i := ιH_inj (code_inj hn23 (by rw [hyj, ← hij, ← hJc i]))
  rw [hyg]
  exact hgcl i (Finset.mem_range.1 hi)

theorem conj_mem_Lbar (c u : ↥HB) (hc : (ιH c) 19 = 19) (hu : (u : ↥NativeSporadic.M23) ∈ Lbar) :
    ((c * u * c⁻¹ : ↥HB) : ↥NativeSporadic.M23) ∈ Lbar := by
  have hs := mem_Gbar_iff.1 (Subgroup.mem_inf.1 c.2).1
  obtain ⟨t19, t21, t22⟩ := mem_Lbar_iff.1 hu
  change ιH u 19 = 19 at t19
  change ιH u 21 = 21 at t21
  change ιH u 22 = 22 at t22
  change ιH c 21 = 21 ∧ ιH c 22 = 22 ∨ ιH c 21 = 22 ∧ ιH c 22 = 21 at hs
  rw [mem_Lbar_iff]
  have e : ∀ p, ((((c * u * c⁻¹ : ↥HB) : ↥NativeSporadic.M23)) : Perm (Fin 23)) p =
      ιH c (ιH u ((ιH c)⁻¹ p)) := fun p => by
    rw [← map_inv, ← Perm.mul_apply, ← Perm.mul_apply, ← map_mul, ← map_mul]
    rfl
  have i19 : (ιH c)⁻¹ 19 = 19 := Perm.inv_eq_iff_eq.2 hc.symm
  rw [e, e, e]
  rcases hs with ⟨s21, s22⟩ | ⟨s21, s22⟩
  · have i21 : (ιH c)⁻¹ 21 = 21 := Perm.inv_eq_iff_eq.2 s21.symm
    have i22 : (ιH c)⁻¹ 22 = 22 := Perm.inv_eq_iff_eq.2 s22.symm
    exact ⟨by rw [i19, t19, hc], by rw [i21, t21]; exact s21, by rw [i22, t22]; exact s22⟩
  · have i21 : (ιH c)⁻¹ 21 = 22 := Perm.inv_eq_iff_eq.2 s22.symm
    have i22 : (ιH c)⁻¹ 22 = 21 := Perm.inv_eq_iff_eq.2 s21.symm
    exact ⟨by rw [i19, t19, hc], by rw [i21, t22]; exact s22, by rw [i22, t21]; exact s21⟩

theorem autH_sound (hcard : Nat.card ↥HB ≤ 1920) (γ : ↥HB →* ↥NativeSporadic.M23)
    (hinj : Function.Injective γ) (hγH : ∀ h, γ h ∈ HB)
    (hγL : ∀ h : ↥HB, (h : ↥NativeSporadic.M23) ∈ Lbar → γ h ∈ Lbar) :
    ∃ g ∈ HB, (g : Perm (Fin 23)) 19 = 19 ∧
      ∀ i : ↥HB, (i : ↥NativeSporadic.M23) ∈ quadStab ↥NativeSporadic.M23 (16 : Fin 23) 19 21 22 ⊓ Gbar →
        γ i = g * i * g⁻¹ := by
  classical
  set γ' : ↥HB →* ↥HB := γ.codRestrict HB hγH with hγ'
  have hγ'c : ∀ z, ((γ' z : ↥HB) : ↥NativeSporadic.M23) = γ z := fun z => rfl
  have hγ'inj : Function.Injective γ' := fun a b h => hinj (by rw [← hγ'c, ← hγ'c, h])
  have hpow : ∀ (z : ↥HB) (k : ℕ), (ιH z) ^ k = 1 ↔ z ^ k = 1 := fun z k => by
    rw [← map_pow, map_eq_one_iff _ ιH_inj]
  have hne : ∀ z : ↥HB, ιH z ≠ 1 ↔ z ≠ 1 := fun z => by rw [Ne, Ne, map_eq_one_iff _ ιH_inj]
  have hpowγ : ∀ (z : ↥HB) (k : ℕ), (γ' z) ^ k = 1 ↔ z ^ k = 1 := fun z k => by
    rw [← map_pow, map_eq_one_iff _ hγ'inj]
  have hneγ : ∀ z : ↥HB, γ' z ≠ 1 ↔ z ≠ 1 := fun z => by rw [Ne, Ne, map_eq_one_iff _ hγ'inj]
  have hcode : ∀ z : ↥HB, code (ιH z) = code ((z : ↥NativeSporadic.M23) : Perm (Fin 23)) :=
    fun z => rfl
  obtain ⟨-, -, h8, h2, h5, hpw, -, -, -, -, -, -⟩ := facts
  rw [e_eq, hA_H] at h8
  rw [e_eq, hB_H] at h2
  rw [e_eq, hA_H, hB_H, code_mul hn23, ← map_mul] at h5
  have ha8' := (ord8K_code hn23 (ιH a')).1 h8
  have hb2' := (ord2K_code hn23 (ιH b')).1 h2
  have hab5' := (ord5K_code hn23 (ιH (a' * b'))).1 h5
  have ha8 : a' ^ 4 ≠ 1 ∧ a' ^ 8 = 1 :=
    ⟨fun h => ha8'.1 ((hpow a' 4).2 h), (hpow a' 8).1 ha8'.2⟩
  have hb2 : b' ≠ 1 ∧ b' ^ 2 = 1 := ⟨(hne b').1 hb2'.1, (hpow b' 2).1 hb2'.2⟩
  have hab5 : a' * b' ≠ 1 ∧ (a' * b') ^ 5 = 1 :=
    ⟨(hne _).1 hab5'.1, (hpow _ 5).1 hab5'.2⟩
  set x := γ' a' with hx
  set y := γ' b' with hy
  obtain ⟨i, hi, hxi⟩ := hall_H hcard x
  have ho := (orbAt_iff _ _ _ _ _ _ _ _ _).1 (CFSG.KS.Raw.Orb.allN_iff.1 ch7108_orb i hi)
  obtain ⟨hci, hrep, hc19, hcx⟩ := ho (by
    rw [e_eq, ← hxi]
    refine (ord8K_code hn23 _).2 ⟨?_, ?_⟩
    · rw [Ne, hpow, hx, hpowγ]
      exact ha8.1
    · rw [hpow, hx, hpowγ]
      exact ha8.2)
  obtain ⟨cH, -, hcH⟩ := htree.1 _ hci
  obtain ⟨rr, hrr, hrr1⟩ := (repIn_iff _ _).1 hrep
  obtain ⟨hrrN, hscan⟩ := (repK_iff _ _ _ _ _ _ _ _ _).1 ((scanK_iff _ _ _ _ _ _ _ _ _).1 ch7108_scan rr hrr)
  obtain ⟨rH, -, hrH⟩ := htree.1 _ hrrN
  have hrH' : code (ιH rH) = tC 23 hT (fl oR 16 i) := by rw [hrH, hrr1]
  rw [← hcH, ← hxi, ← hrH', code_mul hn23, code_mul hn23, ← map_mul, ← map_mul] at hcx
  have hcx' : cH * x = rH * cH := ιH_inj (code_inj hn23 hcx)
  have hrx : rH = cH * x * cH⁻¹ := (eq_mul_inv_of_mul_eq hcx'.symm)
  rw [← hcH] at hc19
  have hc19' : (ιH cH) 19 = 19 := (img_iff _ 19 19).1 hc19
  set y' := cH * y * cH⁻¹ with hy'
  obtain ⟨j, hj, hyj⟩ := hall_H hcard y'
  have hy'2 : y' ≠ 1 ∧ y' ^ 2 = 1 := by
    refine ⟨fun h => ?_, ?_⟩
    · have : y = 1 := by
        have e : y = cH⁻¹ * y' * cH := by rw [hy']; group
        rw [e, h]; group
      exact (hneγ b').2 hb2.1 this
    · rw [hy', conj_pow', hy, (hpowγ b' 2).2 hb2.2]
      group
  have hji : j ∈ i2 := by
    refine (invAt_iff _ _ _ _ _).1 (CFSG.KS.Raw.Orb.allN_iff.1 ch7108_inv j hj) ?_
    rw [e_eq, ← hyj]
    exact (ord2K_code hn23 _).2 ⟨(hne y').2 hy'2.1, (hpow y' 2).2 hy'2.2⟩
  have hry : rH * y' = cH * γ' (a' * b') * cH⁻¹ := by
    rw [hrx, hy', map_mul, ← hx, ← hy]
    group
  have hS := hscan j hji
  rw [← hrH, ← hyj] at hS
  have hconj : ∀ w : List ℕ, prodW (wI [rH, y']) w = cH * γ' (prodW (wI [a', b']) w) * cH⁻¹ := by
    intro w
    have e1 : [rH, y'] = [x, y].map (MulAut.conj cH).toMonoidHom := by
      simp only [List.map_cons, List.map_nil, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hrx,
        hy']
    have e2 : [x, y] = [a', b'].map γ' := rfl
    rw [e1, ← prodW_hom, e2, ← prodW_hom]
    rfl
  have hcodes : [code (ιH rH), code (ιH y')] = [rH, y'].map fun g => code (ιH g) := rfl
  obtain ⟨jg, -, -, hjg2, hjg19, hiw⟩ := hS (by
      rw [e_eq, code_mul hn23, ← map_mul]
      refine (ord5K_code hn23 _).2 ⟨(hne _).2 ?_, (hpow _ 5).2 ?_⟩
      · rw [hry]
        intro h
        have : γ' (a' * b') = 1 := by
          have e : γ' (a' * b') = cH⁻¹ * (cH * γ' (a' * b') * cH⁻¹) * cH := by group
          rw [e, h]; group
        exact (hneγ _).2 hab5.1 this
      · rw [hry, conj_pow', (hpowγ _ 5).2 hab5.2]
        group) (by
      rw [hcodes, pwK_iff]
      intro w hw
      have hwl : ∀ l ∈ w, l < 2 * [rH, y'].length := fun l hl => lt_two _ _ (pW_lt w hw l hl)
      rw [evK_w ιH _ w hwl, hcode, inPbarK_iff, hconj]
      refine ⟨conj_mem_Lbar cH _ hc19' ?_, (Subgroup.mem_inf.1 (cH * γ' _ * cH⁻¹).2).2⟩
      have hp := (pwK_iff _ _ _ _).1 hpw w hw
      rw [hAB_codes, evK_w ιH [a', b'] w fun l hl => lt_two a' b' (pW_lt w hw l hl), hcode,
        inPbarK_iff] at hp
      exact hγL _ hp.1)
  obtain ⟨gH, -, hgH⟩ := htree.1 _ hjg2
  rw [← hgH] at hjg19
  have hg19 : (ιH gH) 19 = 19 := (img_iff _ 19 19).1 hjg19
  rw [hcodes, ← hgH] at hiw
  have hgw : ∀ w ∈ iW, γ' (prodW (wI [a', b']) w) =
      (cH⁻¹ * gH) * prodW (wI [a', b']) w * (cH⁻¹ * gH)⁻¹ := by
    intro w hw
    have hwl : ∀ l ∈ w, l < 2 * [rH, y'].length := fun l hl => lt_two _ _ (iW_lt w hw l hl)
    have h1 := (iwK_iff _ _ _ _ _).1 hiw (w, evK 23 e (withInv 23 [hA, hB]) w)
      (List.mem_map.2 ⟨w, hw, rfl⟩)
    change mul 23 (evK 23 e (withInv 23 ([rH, y'].map fun g => code (ιH g))) w) (code (ιH gH)) =
      mul 23 (code (ιH gH)) (evK 23 e (withInv 23 [hA, hB]) w) at h1
    rw [hAB_codes, evK_w ιH [rH, y'] w hwl,
      evK_w ιH [a', b'] w fun l hl => lt_two a' b' (iW_lt w hw l hl), code_mul hn23,
      code_mul hn23, ← map_mul,
      ← map_mul, hconj] at h1
    have h2 := ιH_inj (code_inj hn23 h1)
    calc γ' (prodW (wI [a', b']) w)
        = cH⁻¹ * ((cH * γ' (prodW (wI [a', b']) w) * cH⁻¹) * gH) * gH⁻¹ * cH := by group
      _ = (cH⁻¹ * gH) * prodW (wI [a', b']) w * (cH⁻¹ * gH)⁻¹ := by rw [h2]; group
  set g' := cH⁻¹ * gH with hg'
  have hle : Subgroup.closure {x | x ∈ gsI} ≤ γ'.eqLocus (MulAut.conj g').toMonoidHom := by
    rw [Subgroup.closure_le]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    change γ' _ = (MulAut.conj g') _
    rw [MulAut.conj_apply]
    exact hgw w hw
  refine ⟨(g' : ↥NativeSporadic.M23), g'.2, ?_, fun i hi => ?_⟩
  · change ιH (cH⁻¹ * gH) 19 = 19
    rw [map_mul, map_inv, Perm.mul_apply, hg19]
    exact Perm.inv_eq_iff_eq.2 hc19'.symm
  · have h1 : γ' i = (MulAut.conj g') i := hle (mem_closure_I hcard i (mem_IxS_of_mem hi))
    rw [MulAut.conj_apply] at h1
    rw [← hγ'c, h1]
    rfl

noncomputable abbrev ιL : ↥Lbar →* Perm (Fin 23) := ιM.comp Lbar.subtype

theorem ιL_inj : Function.Injective ιL := fun _ _ h => Subtype.ext (Subtype.ext h)

noncomputable def gsL : List ↥Lbar :=
  [⟨fAM, F4S_le fA_mem⟩, ⟨fBM, F4S_le fB_mem⟩, ⟨fCM, F4S_le fC_mem⟩, ⟨lXM, lX_mem⟩]

theorem ιL_apply (z : ↥Lbar) : ιL z = ιM (z : ↥NativeSporadic.M23) := rfl

theorem gsL_codes : [fA, fB, fC, lX] = gsL.map fun g => code (ιL g) := by
  rw [gens_eq.2.2.1, gens_eq.2.2.2.1, gens_eq.2.2.2.2, lX_eq, gsL]
  simp only [List.map_cons, List.map_nil, ιL_apply]

theorem ltree : (∀ i < lN, ∃ g ∈ Subgroup.closure {x | x ∈ gsL}, code (ιL g) = tC 23 lT i) ∧
    ∀ i j, i < j → j < lN → tC 23 lT i < tC 23 lT j := by
  refine treeK_sound ιL hn23 (PP := lP) (PD := lD) ?_
    fun i hi => blt_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 ch7108_gidx.2.2 i hi)
  rw [← gsL_codes, ← e_eq]
  exact ch7108_ltree

theorem autL_sound (hcard : Nat.card ↥Lbar = 960) (α : ↥Lbar ≃* ↥Lbar)
    (hα : ∀ f : ↥Lbar, (f : ↥NativeSporadic.M23) ∈ F4S → α f = f) : α = MulEquiv.refl _ := by
  classical
  have hall : ∀ z : ↥Lbar, ∃ k < lN, code (ιL z) = tC 23 lT k :=
    listed_all ιL (fun i hi => (ltree.1 i hi).elim fun g hg => ⟨g, hg.2⟩) ltree.2
      (by rw [ch7108_sizes.2.2, hcard])
  have hcl : ∀ z : ↥Lbar, z ∈ Subgroup.closure {x | x ∈ gsL} := by
    intro z
    obtain ⟨k, hk, hzk⟩ := hall z
    obtain ⟨g, hg, hgk⟩ := ltree.1 k hk
    rw [ιL_inj (code_inj hn23 (hzk.trans hgk.symm))]
    exact hg
  have hpow : ∀ (z : ↥Lbar) (k : ℕ), (ιL z) ^ k = 1 ↔ z ^ k = 1 := fun z k => by
    rw [← map_pow, map_eq_one_iff _ ιL_inj]
  have hne : ∀ z : ↥Lbar, ιL z ≠ 1 ↔ z ≠ 1 := fun z => by rw [Ne, Ne, map_eq_one_iff _ ιL_inj]
  set l' : ↥Lbar := ⟨lXM, lX_mem⟩ with hl'
  have hl'v : (l' : ↥NativeSporadic.M23) = lXM := rfl
  have hl'c : lX = code (ιL l') := by rw [lX_eq, ιL_apply, hl'v]
  set x := α l' with hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h3⟩ := facts
  rw [e_eq, hl'c] at h3
  have hl3 := (ord3K_code hn23 _).1 h3
  rw [hne, hpow] at hl3
  have hx3 : x ≠ 1 ∧ x ^ 3 = 1 := by
    refine ⟨fun h => hl3.1 ((map_eq_one_iff α α.injective).1 h), ?_⟩
    rw [hx, ← map_pow, hl3.2, map_one]
  have hxl : x = l' := by
    by_contra hne'
    obtain ⟨i, hi, hxi⟩ := hall x
    have hA := (autAt_iff _ _ _ _ _ _).1
      (CFSG.KS.Raw.Orb.allN_iff.1 (andB_iff.1 ch7108_aut).1 i hi)
    obtain ⟨r, hr, hsep⟩ := hA (by
        rw [e_eq, ← hxi]
        exact (ord3K_code hn23 _).2 ⟨(hne x).2 hx3.1, (hpow x 3).2 hx3.2⟩)
      (by
        rw [← hxi, hl'c]
        intro h
        exact hne' (ιL_inj (code_inj hn23 h)))
    obtain ⟨hr1, hr2, hf4, hc4, hd0, hd1⟩ := (fwOK_iff _ _ _ _ _).1 (andB_iff.1 ch7108_aut).2 r hr
    obtain ⟨fL, -, hfL⟩ := ltree.1 _ hr1
    obtain ⟨cL, -, hcL⟩ := ltree.1 _ hr2
    rw [← hfL] at hf4
    rw [← hcL] at hc4
    have hαf := hα fL ((inF4K_iff _).1 hf4)
    have hαc := hα cL ((inF4K_iff _).1 hc4)
    obtain ⟨hs0, hs1⟩ := (sepK_iff _ _ _ _ _).1 hsep
    rw [← hxi, ← hfL, ← hcL, code_mul hn23, code_mul hn23, ← map_mul, ← map_mul] at hs0 hs1
    rw [← hfL, ← hcL, hl'c, code_mul hn23, code_mul hn23, ← map_mul, ← map_mul] at hd0 hd1
    by_cases hd : r.2.2 = 0
    · have e1 : cL * l' = l' * fL := ιL_inj (code_inj hn23 (hd0 hd))
      have e2 : cL * x = x * fL := by
        have := congrArg α e1
        rwa [map_mul, map_mul, hαc, hαf] at this
      exact hs0 hd (by rw [e2])
    · have e1 : l' * cL = fL * l' := ιL_inj (code_inj hn23 (hd1 hd))
      have e2 : x * cL = fL * x := by
        have := congrArg α e1
        rwa [map_mul, map_mul, hαc, hαf] at this
      exact hs1 hd (by rw [e2])
  have hle : Subgroup.closure {x | x ∈ gsL} ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    intro z hz
    change α z = z
    simp only [gsL, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hα _ fA_mem
    · exact hα _ fB_mem
    · exact hα _ fC_mem
    · exact hxl
  exact MulEquiv.ext fun z => hle (hcl z)

end CFSG.KD.M23Aut

end
