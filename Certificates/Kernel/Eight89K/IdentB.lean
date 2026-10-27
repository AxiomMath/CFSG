module

public import Certificates.Kernel.Eight89K.CertC
public import Certificates.Kernel.Eight89K.CertD
public import Certificates.Kernel.Eight89K.CertE
public import CFSG.Certificates.Kernel.Eight89K.GRingSound
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KModel

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 CFSG.KC.GRing CFSG.KC.PackPerm
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

public section

namespace CFSG.KC.Eight89K

@[expose] noncomputable def permTab (d : Nat) (t : Array Nat) : Bool :=
  bAnd(allLt d fun x => bAnd(Nat.beq (t.getD x x) (pget (pack8 t.toList) x),
    Nat.blt (pget (pack8 t.toList) x) d), lanesInj d (pack8 t.toList))

theorem tperm_pget {d : Nat} {t : Array Nat} (h : permTab d t = true) (x : Fin d) :
    (tperm d t x : Nat) = pget (pack8 t.toList) x := by
  unfold permTab at h
  rw [bAnd_eq_true, allLt_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hf : ∀ x < d, t.getD x x = pget (pack8 t.toList) x ∧ pget (pack8 t.toList) x < d := by
    intro x hx
    have := h1 x hx
    rw [bAnd_eq_true] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, by simpa using this.2⟩
  unfold lanesInj at h2
  rw [allLt_iff] at h2
  have hlt : ∀ x < d, ∀ y < x, pget (pack8 t.toList) x ≠ pget (pack8 t.toList) y := by
    intro x hx y hy hxy
    have := (allLt_iff _ _).mp (h2 x hx) y hy
    rw [hxy, Nat.beq_refl] at this
    exact Bool.false_ne_true this
  have hperm : CFSG.KS.PK.IsPermN d fun x => t.getD x x := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
    · beta_reduce
      rw [(hf x hx).1]
      exact (hf x hx).2
    · beta_reduce at hxy
      rw [(hf x hx).1, (hf y hy).1] at hxy
      rcases Nat.lt_trichotomy x y with h | h | h
      · exact absurd hxy.symm (hlt y hy x h)
      · exact h
      · exact absurd hxy (hlt x hx y h)
  unfold tperm
  rw [CFSG.KS.PK.permOf_apply hperm]
  exact (hf x x.isLt).1

theorem perm3a_tab : permTab 18 KData.m3aT = true := by decide +kernel

theorem perm3b_tab : permTab 18 KData.m3bT = true := by decide +kernel

theorem perm6a_tab : permTab 162 KData.m6aT = true := by decide +kernel

theorem perm6b_tab : permTab 162 KData.m6bT = true := by decide +kernel

@[expose] def pairsOf : List (List Nat) → List (Nat × Nat)
  | f :: _ :: _ :: _ :: _ :: r => (f.headD 0, f.getLastD 0) :: pairsOf r
  | _ => []

@[expose] def sWord (k : Nat) : List Nat := (List.replicate k [0, 1]).flatten

theorem wordM_append {d : Nat} (σ₀ σ₁ : Equiv.Perm (Fin d)) (u w : List Nat) :
    wordM σ₀ σ₁ (u ++ w) = wordM σ₀ σ₁ u * wordM σ₀ σ₁ w := by
  unfold wordM
  rw [List.map_append, List.prod_append]

theorem wordM_sWord {d : Nat} (σ₀ σ₁ : Equiv.Perm (Fin d)) (k : Nat) :
    wordM σ₀ σ₁ (sWord k) = (gen σ₀ σ₁ 0 * gen σ₀ σ₁ 1) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold sWord at ih ⊢
    rw [List.replicate_succ, List.flatten_cons, wordM_append, ih, pow_succ']
    unfold wordM
    simp

theorem fprod_single {d : Nat} (σ₀ σ₁ : Equiv.Perm (Fin d)) (ws : List (List Nat)) (f : Nat) :
    fprod σ₀ σ₁ ws [f] = wordM σ₀ σ₁ (ws.getD f []) := by
  unfold fprod
  simp

theorem mem_chunks {α : Type} (l : List α) (c n : Nat) (hl : l.length ≤ c * n) {e : α}
    (he : e ∈ l) : ∃ i < n, e ∈ (l.drop (c * i)).take c := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, Nat.zero_mul] at hl
      omega
    · exact h
  have hi : c * (j / c) ≤ j := Nat.mul_div_le j c
  have hr : j - c * (j / c) < c := by
    rw [← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt _ hc
  refine ⟨j / c, Nat.div_lt_of_lt_mul (by omega), ?_⟩
  rw [List.mem_iff_getElem]
  refine ⟨j - c * (j / c), ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_take, List.getElem_drop, Nat.add_sub_of_le hi]

@[expose] noncomputable def s3c : Subgroup.closure ({perm3a, perm3b} : Set (Equiv.Perm (Fin 18))) :=
  gen perm3a perm3b 0 * gen perm3a perm3b 1

@[expose] noncomputable def s6c : Subgroup.closure ({perm6a, perm6b} : Set (Equiv.Perm (Fin 162))) :=
  gen perm6a perm6b 0 * gen perm6a perm6b 1

theorem wordM3 (k : Nat) : wordM perm3a perm3b (sWord k) = s3c ^ k := wordM_sWord _ _ k

theorem wordM6 (k : Nat) : wordM perm6a perm6b (sWord k) = s6c ^ k := wordM_sWord _ _ k

theorem gam_sum {A : Type*} [Ring A] (n : Nat) (X Y : A) :
    sgn (2 * n, false) • (1 : A) + (sgn (n, true) • X + sgn (n, true) • Y) =
      (n : A) * (2 - X - Y) := by
  simp only [sgn, Bool.false_eq_true, ↓reduceIte, zsmul_eq_mul]
  push_cast
  rw [mul_sub, mul_sub, mul_one, neg_mul, neg_mul, (Nat.cast_commute n (2 : A)).eq]
  abel

theorem certC_shape : CFSG.KD.E89C.terms =
    expand 215 (pairsOf CFSG.KD.E89C.terms) ++ [[216], [217]] := by
  decide +kernel

theorem certC_words : CFSG.KD.E89C.ws.getD 215 [] = sWord 3 ∧ CFSG.KD.E89C.ws.getD 216 [] = sWord 5 ∧
    CFSG.KD.E89C.ws.getD 217 [] = sWord 10 := by
  decide +kernel

theorem certD_shape : CFSG.KD.E89D.terms.map Prod.fst =
    expand 67 (pairsOf (CFSG.KD.E89D.terms.map Prod.fst)) := by
  decide +kernel

theorem certD_words : CFSG.KD.E89D.ws.getD 67 [] = sWord 3 ∧
    CFSG.KD.E89D.gm = [([], (21600, false)), (sWord 5, (10800, true)), (sWord 10, (10800, true))] := by
  decide +kernel

theorem certE_shape : CFSG.KD.E89E.terms.map Prod.fst =
    expand 71 (pairsOf (CFSG.KD.E89E.terms.map Prod.fst)) := by
  decide +kernel

theorem certE_words : CFSG.KD.E89E.ws.getD 71 [] = sWord 6 ∧
    CFSG.KD.E89E.gm = [([], (43200, false)), (sWord 10, (21600, true)), (sWord 20, (21600, true))] := by
  decide +kernel

theorem h3a (x : Fin 18) : (perm3a x : Nat) = pget (pack8 KData.m3aT.toList) x := tperm_pget perm3a_tab x

theorem h3b (x : Fin 18) : (perm3b x : Nat) = pget (pack8 KData.m3bT.toList) x := tperm_pget perm3b_tab x

theorem h6a (x : Fin 162) : (perm6a x : Nat) = pget (pack8 KData.m6aT.toList) x :=
  tperm_pget perm6a_tab x

theorem h6b (x : Fin 162) : (perm6b x : Nat) = pget (pack8 KData.m6bT.toList) x :=
  tperm_pget perm6b_tab x

theorem identC_of_card (hM : Nat.card model3 ≤ 1080) : IdentC := by
  obtain ⟨hinj, -⟩ := keyM_injective h3a h3b tree3_ok hM
  have hbs := treeCheck_bsLt tree3_ok
  obtain ⟨we, wc, wc2⟩ := certC_words
  refine ⟨(pairsOf CFSG.KD.E89C.terms).map fun p =>
    (wordM perm3a perm3b (CFSG.KD.E89C.ws.getD p.1 []),
      wordM perm3a perm3b (CFSG.KD.E89C.ws.getD p.2 [])), ?_⟩
  intro A _ h2 ρ
  let ρ' : Subgroup.closure ({perm3a, perm3b} : Set (Equiv.Perm (Fin 18))) →* A := ρ
  have h := sum_eq_zero_of_xor h3a h3b certC_xor hbs hinj A h2 ρ'
  rw [certC_shape, List.map_append, List.sum_append, sum_expand_pairs] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, fprod_single,
    we, wc, wc2, wordM3] at h
  have hc2 : ρ' (s3c ^ 10) = ρ' (s3c ^ 5) ^ 2 := by
    rw [← map_pow, ← pow_mul]
  rw [hc2] at h
  have hY : ρ' (s3c ^ 5) + ρ' (s3c ^ 5) ^ 2 + (ρ' (s3c ^ 5) + ρ' (s3c ^ 5) ^ 2) = 0 := by
    rw [← two_mul, h2, zero_mul]
  exact (eq_neg_of_add_eq_zero_left h).trans (neg_eq_of_add_eq_zero_left hY)

theorem identD_of_card (hM : Nat.card model3 ≤ 1080) : IdentD := by
  obtain ⟨we, wg⟩ := certD_words
  refine ⟨(pairsOf (CFSG.KD.E89D.terms.map Prod.fst)).map fun p =>
    (wordM perm3a perm3b (CFSG.KD.E89D.ws.getD p.1 []),
      wordM perm3a perm3b (CFSG.KD.E89D.ws.getD p.2 [])),
    CFSG.KD.E89D.vt.map fun t => (sgn t.2, wordM perm3a perm3b t.1), ?_⟩
  intro A _ ρ
  have hlen := treeCheck_bs tree3_ok
  have hC : ∀ e ∈ CFSG.KD.E89T3.tree, ∃ es, e ∈ es ∧ sumChunk 18 KData.m3aT.toList KData.m3bT.toList
      CFSG.KD.E89D.V CFSG.KD.E89D.terms CFSG.KD.E89D.gm CFSG.KD.E89T3.bs es = true := by
    intro e he
    obtain ⟨i, hi, hei⟩ := mem_chunks _ 216 5 (by omega) he
    refine ⟨_, hei, ?_⟩
    interval_cases i
    · exact certDChunk0
    · exact certDChunk1
    · exact certDChunk2
    · exact certDChunk3
    · exact certDChunk4
  let ρ' : Subgroup.closure ({perm3a, perm3b} : Set (Equiv.Perm (Fin 18))) →* A := ρ
  have h := prod_eq_of_checks h3a h3b tree3_ok hM certD_tabs certD_v certD_root hC A ρ'
  have hl : (CFSG.KD.E89D.terms.map fun t => ρ' (fprod perm3a perm3b CFSG.KD.E89D.ws t.1)) =
      (CFSG.KD.E89D.terms.map Prod.fst).map fun fs => ρ' (fprod perm3a perm3b CFSG.KD.E89D.ws fs) := by
    rw [List.map_map]
    rfl
  have hv : (CFSG.KD.E89D.vt.map fun t => sgn t.2 • ρ' (wordM perm3a perm3b t.1)) =
      (CFSG.KD.E89D.vt.map fun t => (sgn t.2, wordM perm3a perm3b t.1)).map
        fun x => x.1 • ρ' x.2 := by
    rw [List.map_map]
    rfl
  rw [hl, hv, certD_shape, sum_expand_pairs, we, wordM3, wg] at h
  refine h.trans ?_
  change _ = (10800 : A) * (2 - ρ' (s3c ^ 5) - ρ' (s3c ^ 5) ^ 2)
  have hw : wordM perm3a perm3b [] = 1 := rfl
  have hc2 : ρ' (s3c ^ 10) = ρ' (s3c ^ 5) ^ 2 := by
    rw [← map_pow, ← pow_mul]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sgn, wordM3, hw,
    map_one, hc2]
  have h10 : (10800 : A) = ((10800 : Nat) : A) := by norm_num
  rw [h10]
  exact gam_sum 10800 _ _

theorem identE_of_card (hM : Nat.card model6 ≤ 2160) : IdentE := by
  obtain ⟨we, wg⟩ := certE_words
  refine ⟨(pairsOf (CFSG.KD.E89E.terms.map Prod.fst)).map fun p =>
    (wordM perm6a perm6b (CFSG.KD.E89E.ws.getD p.1 []),
      wordM perm6a perm6b (CFSG.KD.E89E.ws.getD p.2 [])),
    CFSG.KD.E89E.vt.map fun t => (sgn t.2, wordM perm6a perm6b t.1), ?_⟩
  intro A _ ρ
  have hlen := treeCheck_bs tree6_ok
  have hC : ∀ e ∈ CFSG.KD.E89T6.tree, ∃ es, e ∈ es ∧ sumChunk 162 KData.m6aT.toList KData.m6bT.toList
      CFSG.KD.E89E.V CFSG.KD.E89E.terms CFSG.KD.E89E.gm CFSG.KD.E89T6.bs es = true := by
    intro e he
    obtain ⟨i, hi, hei⟩ := mem_chunks _ 216 10 (by omega) he
    refine ⟨_, hei, ?_⟩
    interval_cases i
    · exact certEChunk0
    · exact certEChunk1
    · exact certEChunk2
    · exact certEChunk3
    · exact certEChunk4
    · exact certEChunk5
    · exact certEChunk6
    · exact certEChunk7
    · exact certEChunk8
    · exact certEChunk9
  let ρ' : Subgroup.closure ({perm6a, perm6b} : Set (Equiv.Perm (Fin 162))) →* A := ρ
  have h := prod_eq_of_checks h6a h6b tree6_ok hM certE_tabs certE_v certE_root hC A ρ'
  have hl : (CFSG.KD.E89E.terms.map fun t => ρ' (fprod perm6a perm6b CFSG.KD.E89E.ws t.1)) =
      (CFSG.KD.E89E.terms.map Prod.fst).map fun fs => ρ' (fprod perm6a perm6b CFSG.KD.E89E.ws fs) := by
    rw [List.map_map]
    rfl
  have hv : (CFSG.KD.E89E.vt.map fun t => sgn t.2 • ρ' (wordM perm6a perm6b t.1)) =
      (CFSG.KD.E89E.vt.map fun t => (sgn t.2, wordM perm6a perm6b t.1)).map
        fun x => x.1 • ρ' x.2 := by
    rw [List.map_map]
    rfl
  rw [hl, hv, certE_shape, sum_expand_pairs, we, wordM6, wg] at h
  refine h.trans ?_
  change _ = (21600 : A) * (2 - ρ' (s6c ^ 10) - ρ' (s6c ^ 10) ^ 2)
  have hw : wordM perm6a perm6b [] = 1 := rfl
  have hz2 : ρ' (s6c ^ 20) = ρ' (s6c ^ 10) ^ 2 := by
    rw [← map_pow, ← pow_mul]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sgn, wordM6, hw,
    map_one, hz2]
  have h10 : (21600 : A) = ((21600 : Nat) : A) := by norm_num
  rw [h10]
  exact gam_sum 21600 _ _

end CFSG.KC.Eight89K

end
