module

public import Certificates.Kernel.HS4062.H
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert
public import Certificates.Kernel.HS4062.O

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS4062.F

open CFSG.KD.HS4062 CFSG.KC.Kc3K CFSG.KC.Enum CFSG.KD.E16 CFSG.KD.E16L CFSG.KD.HS4062.H
open CFSG.Sporadic.Schreier (hsP card_hsP)
open CFSG.QuasithinUnique.K1.SporadicPerm (act act_mul act_one act_lt act_eq)

theorem fibk {k : Nat} (hk : k < 8) :
    maskL (EL k) = EM.getD k 0 ∧ (EL k).length = 15 ∧ (EL k).Nodup ∧ (∀ i ∈ EL k, i < 87) ∧
      (k ≠ 0 → k ≠ 5 → ∀ x ∈ EL k, ((EL k).filter fun y => (FL y).length == (FL x).length).length <
        10) := by
  have hf := List.all_eq_true.1 fib k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at hf
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hf
  refine ⟨h1, h2, (chainLt_sorted _ h3).imp (fun h => h.ne), h4, fun h0 h5' => ?_⟩
  rcases h5 with (h5 | h5) | h5
  · exact absurd h5 h0
  · exact absurd h5 h5'
  · exact fbK_spec h5

theorem clsk {k : Nat} (hk : k < 8) : ∀ i ∈ EL k, ∀ j ∈ EL k, i ≠ j → pr i j ∈ EL k :=
  (clsK_spec (List.all_eq_true.1 cls k (List.mem_range.2 hk))).2.2

theorem lt_of_EL {k : Nat} (hk : k < 8) {i : Nat} (hi : i ∈ EL k) : i < 87 := (fibk hk).2.2.2.1 i hi

theorem V_mulk {k : Nat} (hk : k < 8) {i j : Nat} (hi : i ∈ EL k) (hj : j ∈ EL k) (hij : i ≠ j) :
    Vi (pr i j) = Vi i * Vi j ∧ Vi i * Vi j = Vi j * Vi i :=
  V_mul ctx checks (lt_of_EL hk hi) (lt_of_EL hk hj) hij (lt_of_EL hk (clsk hk i hi j hj hij))

@[expose] noncomputable def S (k : Nat) : Set ↥hsP := {y | y = 1 ∨ ∃ i ∈ EL k, Vi i = y}

theorem S_eq (k : Nat) : S k = ↑((1 :: (EL k).map Vi).toFinset) := by
  ext y
  simp only [S, Set.mem_setOf_eq, Finset.coe_insert, List.toFinset_cons, Finset.mem_coe,
    List.mem_toFinset, List.mem_map, Set.mem_insert_iff]

theorem S_finite (k : Nat) : (S k).Finite := by
  rw [S_eq]
  exact Finset.finite_toSet _

theorem S_ncard {k : Nat} (hk : k < 8) : (S k).ncard ≤ 16 := by
  rw [S_eq, Set.ncard_coe_finset]
  refine (List.toFinset_card_le _).trans ?_
  simp [(fibk hk).2.1]

theorem S_ncard_eq {k : Nat} (hk : k < 8) : (S k).ncard = 16 := by
  classical
  rw [S_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
  · simp [(fibk hk).2.1]
  · refine List.nodup_cons.2 ⟨fun h => ?_, ?_⟩
    · obtain ⟨i, hi, e⟩ := List.mem_map.1 h
      exact V_ne_one ctx checks (lt_of_EL hk hi) e
    · exact (fibk hk).2.2.1.map_on fun i hi j hj e =>
        V_inj ctx checks (lt_of_EL hk hi) (lt_of_EL hk hj) e

theorem eq_S {k : Nat} (hk : k < 8) (E : Subgroup ↥hsP) (hE : ∀ x ∈ E, x ≠ 1 → ∃ i ∈ EL k, Vi i = x)
    (hcard : Nat.card E = 16) : (E : Set ↥hsP) = S k := by
  refine Set.eq_of_subset_of_ncard_le (fun x hx => ?_) ?_ (S_finite k)
  · by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hE x hx h1)
  · have h16 : (E : Set ↥hsP).ncard = 16 := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard]
    rw [h16]
    exact S_ncard hk

@[expose] noncomputable def E5 : Subgroup ↥hsP where
  carrier := S 5
  mul_mem' := by
    rintro x y (rfl | ⟨i, hi, rfl⟩) (rfl | ⟨j, hj, rfl⟩)
    · exact Or.inl (one_mul 1)
    · rw [one_mul]
      exact Or.inr ⟨j, hj, rfl⟩
    · rw [mul_one]
      exact Or.inr ⟨i, hi, rfl⟩
    · by_cases hij : i = j
      · subst hij
        exact Or.inl (V_sq ctx checks (lt_of_EL (by norm_num) hi))
      · exact Or.inr ⟨pr i j, clsk (by norm_num) i hi j hj hij,
          (V_mulk (by norm_num) hi hj hij).1⟩
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inl inv_one
    · refine Or.inr ⟨i, hi, ?_⟩
      exact (inv_eq_of_mul_eq_one_right (V_sq ctx checks (lt_of_EL (by norm_num) hi))).symm

theorem card_E5 : Nat.card E5 = 16 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact S_ncard_eq (by norm_num)

theorem comm_E5 : ∀ x ∈ E5, ∀ y ∈ E5, x * y = y * x := by
  rintro x (rfl | ⟨i, hi, rfl⟩) y (rfl | ⟨j, hj, rfl⟩)
  · rfl
  · rw [one_mul, mul_one]
  · rw [one_mul, mul_one]
  · by_cases hij : i = j
    · rw [hij]
    · exact (V_mulk (by norm_num) hi hj hij).2

@[expose] noncomputable def s (u : Nat) : ↥hsP := if u = 0 then 1 else Vi ((0 :: EL 5).getD u 0)

theorem SL_mem {u : Nat} (hu0 : 0 < u) (hu : u < 16) : (0 :: EL 5).getD u 0 ∈ EL 5 := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  rw [List.getD_cons_succ, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [(fibk (by norm_num : 5 < 8)).2.1]; omega), Option.getD_some]
  exact List.getElem_mem _

theorem s_mem {u : Nat} (hu : u < 16) : s u ∈ E5 := by
  unfold s
  split_ifs with h
  · exact E5.one_mem
  · exact Or.inr ⟨_, SL_mem (by omega) hu, rfl⟩

theorem s_ne {u : Nat} (hu0 : 0 < u) (hu : u < 16) :
    s u = Vi ((0 :: EL 5).getD u 0) := by
  unfold s
  rw [if_neg (by omega)]

theorem exists_s {x : ↥hsP} (hx : x ∈ E5) : ∃ u < 16, s u = x := by
  rcases hx with rfl | ⟨i, hi, rfl⟩
  · exact ⟨0, by norm_num, rfl⟩
  · obtain ⟨v, hv, e⟩ := List.getElem_of_mem hi
    have hv' : v < 15 := by rwa [(fibk (by norm_num : 5 < 8)).2.1] at hv
    refine ⟨v + 1, by omega, ?_⟩
    rw [s_ne (by omega) (by omega), List.getD_cons_succ, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hv, Option.getD_some, e]

theorem s_inj {u v : Nat} (hu : u < 16) (hv : v < 16) (h : s u = s v) : u = v := by
  rcases Nat.eq_zero_or_pos u with rfl | hu0 <;> rcases Nat.eq_zero_or_pos v with rfl | hv0
  · rfl
  · rw [s_ne hv0 hv] at h
    exact absurd h.symm (V_ne_one ctx checks (lt_of_EL (by norm_num) (SL_mem hv0 hv)))
  · rw [s_ne hu0 hu] at h
    exact absurd h (V_ne_one ctx checks (lt_of_EL (by norm_num) (SL_mem hu0 hu)))
  · rw [s_ne hu0 hu, s_ne hv0 hv] at h
    have e := V_inj ctx checks (lt_of_EL (by norm_num) (SL_mem hu0 hu))
      (lt_of_EL (by norm_num) (SL_mem hv0 hv)) h
    obtain ⟨u', rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
    obtain ⟨v', rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    have h15 := (fibk (by norm_num : 5 < 8)).2.1
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some] at e
    have := (List.Nodup.getElem_inj_iff (fibk (by norm_num : 5 < 8)).2.2.1).1 e
    omega

@[expose] noncomputable def idx (x : ↥hsP) : Nat :=
  open scoped Classical in if h : ∃ u < 16, s u = x then Classical.choose h else 0

theorem idx_spec {x : ↥hsP} (hx : x ∈ E5) : idx x < 16 ∧ s (idx x) = x := by
  classical
  have h := exists_s hx
  unfold idx
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem idx_s {u : Nat} (hu : u < 16) : idx (s u) = u :=
  s_inj (idx_spec (s_mem hu)).1 hu (idx_spec (s_mem hu)).2

@[expose] noncomputable def nG (t : Nat) : ↥hsP := G.E (NG.getD t 0)

theorem cj_spec {t : Nat} (ht : t < 3) :
    (PI t).length = 16 ∧ (PI t).getD 0 0 = 0 ∧ ∀ u, 0 < u → u < 16 →
      0 < (PI t).getD u 0 ∧ (PI t).getD u 0 < 16 ∧ ∀ b ∈ B,
        pg 12 4095 (TF (NG.getD t 0)) (ivA 12 4095 TF vu vv ((0 :: EL 5).getD u 0) b) =
          ivA 12 4095 TF vu vv ((0 :: EL 5).getD ((PI t).getD u 0) 0)
            (pg 12 4095 (TF (NG.getD t 0)) b) :=
  cjEK_spec (List.all_eq_true.1 conj t (List.mem_range.2 ht))

theorem PI_lt {t : Nat} (ht : t < 3) {u : Nat} (hu : u < 16) : (PI t).getD u 0 < 16 := by
  rcases Nat.eq_zero_or_pos u with rfl | hu0
  · rw [(cj_spec ht).2.1]
    norm_num
  · exact ((cj_spec ht).2.2 u hu0 hu).2.1

theorem node_lt {t : Nat} (ht : t < 3) : NG.getD t 0 < 203 :=
  ngLt _ (by rw [List.getD_eq_getElem _ _ (by rw [ngLen]; exact ht)]; exact List.getElem_mem _)

theorem act_Vi {i : Nat} (hi : i < 87) {p : Nat} (hp : p < 3850) :
    act 3850 (Vi i) p = ivA 12 4095 TF vu vv i p :=
  act_V ctx checks hi hp

theorem conj_s {t : Nat} (ht : t < 3) {u : Nat} (hu : u < 16) :
    nG t * s u * (nG t)⁻¹ = s ((PI t).getD u 0) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu0
  · rw [(cj_spec ht).2.1]
    simp [s]
  obtain ⟨h1, h2, h3⟩ := (cj_spec ht).2.2 u hu0 hu
  rw [mul_inv_eq_iff_eq_mul, s_ne hu0 hu, s_ne h1 h2]
  refine eq_of_base ctx checks fun p hp => ?_
  have hp' : p < 3850 := checks.hB p hp
  have hq := act_lt (nG t) hp'
  have hi := lt_of_EL (by norm_num) (SL_mem hu0 hu)
  have hj := lt_of_EL (by norm_num) (SL_mem h1 h2)
  change act 3850 (nG t * Vi _) p = act 3850 (Vi _ * nG t) p
  rw [act_mul _ _ hp', act_mul _ _ hp', act_Vi hi hp', act_Vi hj hq]
  unfold nG
  rw [ctx.actE _ (node_lt ht) _ (by rw [← act_Vi hi hp']; exact act_lt _ hp'),
    ctx.actE _ (node_lt ht) _ hp']
  exact h3 p hp

@[expose] noncomputable def N0 : Subgroup ↥hsP :=
  Subgroup.closure ((E5 : Set ↥hsP) ∪ {y | ∃ t < 3, nG t = y})

theorem E5_le_N0 : E5 ≤ N0 := fun x hx => Subgroup.subset_closure (Or.inl hx)

theorem nG_mem {t : Nat} (ht : t < 3) : nG t ∈ N0 := Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)

theorem N0_le : N0 ≤ Subgroup.normalizer (E5 : Set ↥hsP) := by
  rw [N0, Subgroup.closure_le]
  rintro y (hy | ⟨t, ht, rfl⟩)
  · exact Subgroup.le_normalizer hy
  · refine CFSG.QuasithinUnique.A5.Kc3Cert.mem_normalizer_of_conj_le fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := exists_s hx
    rw [conj_s ht hu]
    exact s_mem (PI_lt ht hu)

theorem conj_mem {g : ↥hsP} (hg : g ∈ Subgroup.normalizer (E5 : Set ↥hsP)) {x : ↥hsP}
    (hx : x ∈ E5) : g * x * g⁻¹ ∈ E5 :=
  (Subgroup.mem_normalizer_iff.1 hg x).1 hx

@[expose] noncomputable def dC (g : ↥hsP) : Nat :=
  packL 4 ((List.range 16).map fun u => idx (g * s u * g⁻¹))

theorem lt16_pow : (16 : Nat) = 2 ^ 4 := by norm_num

theorem dC_one : dC 1 = zRoot := by
  unfold dC zRoot
  refine congrArg (packL 4) ?_
  conv_rhs => rw [← List.map_id (List.range 16)]
  refine List.map_congr_left fun u hu => ?_
  rw [one_mul, inv_one, mul_one, idx_s (List.mem_range.1 hu)]
  rfl

theorem dC_list {g : ↥hsP} (hg : g ∈ Subgroup.normalizer (E5 : Set ↥hsP)) :
    ∀ x ∈ (List.range 16).map (fun u => idx (g * s u * g⁻¹)), x < 2 ^ 4 := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
  rw [← lt16_pow]
  exact (idx_spec (conj_mem hg (s_mem (List.mem_range.1 hu)))).1

theorem dC_step {t : Nat} (ht : t < 3) {g : ↥hsP} (hg : g ∈ Subgroup.normalizer (E5 : Set ↥hsP)) :
    dC (nG t * g) = appZ t (dC g) := by
  unfold appZ appP dC
  have hlen : ((List.range 16).map fun u => idx (g * s u * g⁻¹)).length = 16 := by simp
  have hd := decL_packL (w := 4) (m := 15) (by norm_num) (dC_list hg)
  rw [hlen] at hd
  rw [hd, List.map_map]
  refine congrArg (packL 4) (List.map_congr_left fun u hu => ?_)
  have hu' := List.mem_range.1 hu
  obtain ⟨hv, hsv⟩ := idx_spec (conj_mem hg (s_mem hu'))
  have hPI : ∀ x ∈ PI t, x < 2 ^ 4 := by
    intro x hx
    obtain ⟨v, hv1, rfl⟩ := List.getElem_of_mem hx
    have hl := (cj_spec ht).1
    have := PI_lt ht (u := v) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv1, Option.getD_some] at this
    rw [← lt16_pow]
    exact this
  simp only [Function.comp_apply]
  rw [pg_packL (by norm_num) (PI t) hPI _ (by rw [(cj_spec ht).1]; exact hv)]
  have e : nG t * g * s u * (nG t * g)⁻¹ = nG t * s (idx (g * s u * g⁻¹)) * (nG t)⁻¹ := by
    rw [hsv]
    group
  rw [e, conj_s ht hv, idx_s (PI_lt ht hv)]

theorem exists_g : ∃ g : Fin 720 → ↥hsP, (∀ j, g j ∈ N0) ∧
    ∀ i j, (g i)⁻¹ * g j ∈ Subgroup.centralizer (E5 : Set ↥hsP) → i = j := by
  have hS := (trK_sound (g := 3) (M := 720) (app := appZ) (E := ZT) (PG := ZP) (o := zRoot)
    (fun j hj => by
      have hc : j / 240 < 3 := by omega
      have h := CFSG.KD.HS4062.Z.all (j / 240) hc
      unfold famZ at h
      have := List.all_eq_true.1 h (j % 240) (List.mem_range.2 (chunk (by norm_num) j).2)
      rwa [(chunk (by norm_num) j).1] at this)
    (fun c => ∃ g ∈ N0, dC g = c) ⟨1, N0.one_mem, dC_one⟩ (fun t ht c ⟨g, hg, e⟩ =>
      ⟨nG t * g, N0.mul_mem (nG_mem ht) hg, by rw [dC_step ht (N0_le hg), e]⟩))
  choose g hg hgd using fun j : Fin 720 => hS.1 j.1 j.2
  refine ⟨g, hg, fun i j hc => Fin.ext (hS.2 i.1 i.2 j.1 j.2 ?_)⟩
  rw [← hgd i, ← hgd j]
  have hi := N0_le (hg i)
  have hj := N0_le (hg j)
  unfold dC
  refine congrArg (packL 4) (List.map_congr_left fun u hu => ?_)
  have hsu := s_mem (List.mem_range.1 hu)
  have e := (Subgroup.mem_centralizer_iff.1 hc) (s u) hsu
  have e2 : g j * s u * (g j)⁻¹ = g i * s u * (g i)⁻¹ := by
    have e3 : g j * s u * (g j)⁻¹ =
        g i * (((g i)⁻¹ * g j) * s u) * ((g i)⁻¹ * g j)⁻¹ * (g i)⁻¹ := by group
    rw [e3, ← e]
    group
  rw [e2]

theorem card_mul_le (X : Finset ↥hsP) (hX : ∀ x ∈ X, x ∈ N0 ∧ x ∈ Subgroup.centralizer (E5 : Set ↥hsP)) :
    720 * X.card ≤ Nat.card N0 := by
  obtain ⟨g, hg, hinj⟩ := exists_g
  let f : Fin 720 × X → N0 := fun p => ⟨g p.1 * p.2, N0.mul_mem (hg p.1) (hX p.2 p.2.2).1⟩
  have hf : Function.Injective f := by
    rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ e
    have e1 : g i * x = g j * y := congrArg Subtype.val e
    have hij : i = j := by
      apply hinj
      have e2 : (g i)⁻¹ * g j = x * y⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← e1]
        group
      rw [e2]
      exact Subgroup.mul_mem _ (hX x hx).2 (Subgroup.inv_mem _ (hX y hy).2)
    subst hij
    have : x = y := mul_left_cancel e1
    subst this
    rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
    Fintype.card_coe] at this

@[expose, irreducible] noncomputable def T : List Nat := fixE FL FM (EL 5)

theorem EL5_cons : ∃ i L, EL 5 = i :: L := by
  have h := (fibk (by norm_num : 5 < 8)).2.1
  rcases h' : EL 5 with _ | ⟨i, L⟩
  · rw [h'] at h
    simp at h
  · exact ⟨i, L, rfl⟩

theorem FM_eq {i : Nat} (hi : i < 87) : FM i = maskL (FL i) :=
  (ivK_spec (checks.ivc i hi)).2.2.2.2.2.2.2.2.2

theorem T_spec : T.Nodup ∧ ∀ p, p ∈ T ↔ p < 3850 ∧ ∀ x ∈ E5, act 3850 x p = p := by
  obtain ⟨i, L, hEL⟩ := EL5_cons
  have hi : i < 87 := lt_of_EL (k := 5) (by norm_num) (by rw [hEL]; exact List.mem_cons_self)
  have hFL := FL_spec ctx checks hi
  have hspec := fixE_spec (FM := FM) (L := L) hFL.1
  unfold T
  rw [hEL]
  refine ⟨hspec.1, fun p => ?_⟩
  rw [hspec.2 p]
  constructor
  · rintro ⟨hp, hall⟩
    have hp' := hFL.2.1 p hp
    refine ⟨hp', ?_⟩
    rintro x (rfl | ⟨j, hj, rfl⟩)
    · exact act_one hp'
    · rw [hEL] at hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact (hFL.2.2 p hp').1 hp
      · have hj' : j < 87 := lt_of_EL (k := 5) (by norm_num) (by rw [hEL]; exact List.mem_cons_of_mem _ hj)
        have := hall j hj
        rw [FM_eq hj', testBit_maskL] at this
        exact ((FL_spec ctx checks hj').2.2 p hp').1 this
  · rintro ⟨hp, hall⟩
    refine ⟨(hFL.2.2 p hp).2 (hall _ (Or.inr ⟨i, by rw [hEL]; exact List.mem_cons_self, rfl⟩)),
      fun j hj => ?_⟩
    have hj' : j < 87 := lt_of_EL (k := 5) (by norm_num) (by rw [hEL]; exact List.mem_cons_of_mem _ hj)
    rw [FM_eq hj', testBit_maskL]
    exact ((FL_spec ctx checks hj').2.2 p hp).2
      (hall _ (Or.inr ⟨j, by rw [hEL]; exact List.mem_cons_of_mem _ hj, rfl⟩))

theorem T_lt : ∀ p ∈ T, p < 3850 := fun p hp => ((T_spec.2 p).1 hp).1

theorem T_len : T.length = 16 := by
  unfold T
  exact fix

@[expose] noncomputable def oC (g : ↥hsP) : Nat := packL 12 (sortK (T.map (act 3850 g)))

theorem sortK_sortK (l : List Nat) : sortK (sortK l) = sortK l := sortK_of_perm (sortK_perm l)

theorem oC_one : oC 1 = oRoot := by
  unfold oC oRoot
  have e : T.map (act 3850 (1 : ↥hsP)) = T := by
    conv_rhs => rw [← List.map_id T]
    exact List.map_congr_left fun p hp => act_one (T_lt p hp)
  rw [e]
  unfold T
  obtain ⟨i, L, hEL⟩ := EL5_cons
  rw [hEL]
  change packL 12 (sortK (sortK _)) = packL 12 (sortK _)
  rw [sortK_sortK]

theorem img_lt (g : ↥hsP) : ∀ x ∈ sortK (T.map (act 3850 g)), x < 2 ^ 12 := by
  intro x hx
  rw [(sortK_perm _).mem_iff] at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact lt_of_lt_of_le (act_lt g (T_lt p hp)) (by norm_num)

theorem oC_step {t : Nat} (ht : t < 2) (g : ↥hsP) : oC (G.E t * g) = appO t (oC g) := by
  unfold appO appS oC
  have hlen : (sortK (T.map (act 3850 g))).length = 16 := by
    rw [(sortK_perm _).length_eq, List.length_map, T_len]
  have hd := decL_packL (w := 12) (m := 4095) (by norm_num) (img_lt g)
  rw [hlen] at hd
  rw [hd]
  refine congrArg (packL 12) ?_
  have e : (sortK (T.map (act 3850 g))).map (pg 12 4095 (TF t)) =
      (sortK (T.map (act 3850 g))).map (act 3850 (G.E t)) := by
    refine List.map_congr_left fun x hx => ?_
    rw [(sortK_perm _).mem_iff] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact (G.act_node (by omega) (act_lt g (T_lt p hp))).symm
  rw [e]
  refine sortK_of_perm ?_
  have h1 : ((sortK (T.map (act 3850 g))).map (act 3850 (G.E t))).Perm
      ((T.map (act 3850 g)).map (act 3850 (G.E t))) := (sortK_perm _).map _
  have h2 : (T.map (act 3850 g)).map (act 3850 (G.E t)) = T.map (act 3850 (G.E t * g)) := by
    rw [List.map_map]
    exact List.map_congr_left fun p hp => (act_mul _ _ (T_lt p hp)).symm
  exact (h1.trans (List.Perm.of_eq h2)).symm

theorem oC_eq {g h : ↥hsP} (hν : g⁻¹ * h ∈ Subgroup.normalizer (E5 : Set ↥hsP)) : oC g = oC h := by
  unfold oC
  refine congrArg (packL 12) (sortK_of_perm ?_)
  set ν := g⁻¹ * h with hνdef
  have hh : h = g * ν := by rw [hνdef]; group
  have hmem : ∀ {ν : ↥hsP}, ν ∈ Subgroup.normalizer (E5 : Set ↥hsP) → ∀ p ∈ T,
      act 3850 ν p ∈ T := by
    intro ν hν p hp
    obtain ⟨hp1, hp2⟩ := (T_spec.2 p).1 hp
    refine (T_spec.2 _).2 ⟨act_lt _ hp1, fun x hx => ?_⟩
    have hx' : ν⁻¹ * x * ν ∈ E5 := by
      have := conj_mem (inv_mem hν) hx
      simpa using this
    have e : x * ν = ν * (ν⁻¹ * x * ν) := by group
    calc act 3850 x (act 3850 ν p) = act 3850 (x * ν) p := (act_mul _ _ hp1).symm
      _ = act 3850 (ν * (ν⁻¹ * x * ν)) p := by rw [e]
      _ = act 3850 ν p := by rw [act_mul _ _ hp1, hp2 _ hx']
  have hperm : (T.map (act 3850 ν)).Perm T := by
    refine (List.perm_ext_iff_of_nodup (T_spec.1.map_on fun p hp q hq e => ?_) T_spec.1).2
      fun q => ⟨fun hq => ?_, fun hq => ?_⟩
    · have := congrArg (act 3850 ν⁻¹) e
      rwa [← act_mul _ _ (T_lt p hp), ← act_mul _ _ (T_lt q hq), inv_mul_cancel, act_one (T_lt p hp),
        act_one (T_lt q hq)] at this
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact hmem hν p hp
    · refine List.mem_map.2 ⟨act 3850 ν⁻¹ q, hmem (inv_mem hν) q hq, ?_⟩
      rw [← act_mul _ _ (T_lt q hq), mul_inv_cancel, act_one (T_lt q hq)]
  rw [hh]
  have e : T.map (act 3850 (g * ν)) = (T.map (act 3850 ν)).map (act 3850 g) := by
    rw [List.map_map]
    exact List.map_congr_left fun p hp => act_mul _ _ (T_lt p hp)
  rw [e]
  exact (hperm.map _).symm

theorem card_N_le : Nat.card (Subgroup.normalizer (E5 : Set ↥hsP)) ≤ 11520 := by
  have hS := (trK_sound (g := 2) (M := 3850) (app := appO) (E := OT) (PG := OP) (o := oRoot)
    (fun j hj => by
      have hc : j / 256 < 16 := by omega
      have h := CFSG.KD.HS4062.O.all (j / 256) hc
      unfold famO at h
      have := List.all_eq_true.1 h (j % 256) (List.mem_range.2 (chunk (by norm_num) j).2)
      rw [(chunk (by norm_num) j).1] at this
      simpa [hj] using this)
    (fun c => ∃ g : ↥hsP, oC g = c) ⟨1, oC_one⟩ (fun t ht c ⟨g, e⟩ =>
      ⟨G.E t * g, by rw [oC_step ht g, e]⟩))
  choose g hgd using fun j : Fin 3850 => hS.1 j.1 j.2
  set N := Subgroup.normalizer (E5 : Set ↥hsP)
  let f : Fin 3850 → ↥hsP ⧸ N := fun j => (QuotientGroup.mk (g j) : ↥hsP ⧸ N)
  have hf : Function.Injective f := by
    intro i j e
    have hq : (g i)⁻¹ * g j ∈ N := QuotientGroup.eq.1 e
    exact Fin.ext (hS.2 i.1 i.2 j.1 j.2 (by rw [← hgd i, ← hgd j]; exact oC_eq hq))
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [card_hsP] at h2
  by_contra! hc
  have : 3850 * 11521 ≤ Nat.card (↥hsP ⧸ N) * Nat.card N := Nat.mul_le_mul h1 hc
  omega

theorem card_N0_ge : 11520 ≤ Nat.card N0 := by
  classical
  have h := card_mul_le (Set.toFinset (E5 : Set ↥hsP)) fun x hx => by
    rw [Set.mem_toFinset] at hx
    exact ⟨E5_le_N0 hx, Subgroup.mem_centralizer_iff.2 fun y hy => (comm_E5 y hy x hx)⟩
  have hc : (Set.toFinset (E5 : Set ↥hsP)).card = 16 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, SetLike.coe_sort_coe, card_E5]
  rw [hc] at h
  exact h

theorem N0_eq : N0 = Subgroup.normalizer (E5 : Set ↥hsP) :=
  Subgroup.eq_of_le_of_card_ge N0_le (le_trans card_N_le card_N0_ge)

theorem locHypD_E5 : CFSG.QuasithinUnique.A5.LocHypD E5 := by
  classical
  refine ⟨fun x hx => ?_, ?_⟩
  · by_contra hxE
    have hxN : x ∈ N0 := by
      rw [N0_eq]
      refine CFSG.QuasithinUnique.A5.Kc3Cert.mem_normalizer_of_conj_le fun y hy => ?_
      rw [← (Subgroup.mem_centralizer_iff.1 hx) y hy, mul_inv_cancel_right]
      exact hy
    let X : Finset ↥hsP := Set.toFinset (E5 : Set ↥hsP) ∪ (Set.toFinset (E5 : Set ↥hsP)).image (x * ·)
    have hX : ∀ y ∈ X, y ∈ N0 ∧ y ∈ Subgroup.centralizer (E5 : Set ↥hsP) := by
      intro y hy
      have hE : ∀ z ∈ E5, z ∈ Subgroup.centralizer (E5 : Set ↥hsP) := fun z hz =>
        Subgroup.mem_centralizer_iff.2 fun w hw => comm_E5 w hw z hz
      rcases Finset.mem_union.1 hy with hy | hy
      · rw [Set.mem_toFinset] at hy
        exact ⟨E5_le_N0 hy, hE y hy⟩
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
        rw [Set.mem_toFinset] at hz
        exact ⟨N0.mul_mem hxN (E5_le_N0 hz), Subgroup.mul_mem _ hx (hE z hz)⟩
    have hdisj : Disjoint (Set.toFinset (E5 : Set ↥hsP))
        ((Set.toFinset (E5 : Set ↥hsP)).image (x * ·)) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy'
      rw [Set.mem_toFinset] at hy hz
      apply hxE
      have := E5.mul_mem hy (E5.inv_mem hz)
      simpa using this
    have hc16 : (Set.toFinset (E5 : Set ↥hsP)).card = 16 := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, SetLike.coe_sort_coe, card_E5]
    have hcX : X.card = 32 := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (mul_right_injective x),
        hc16]
    have h1 := card_mul_le X hX
    rw [hcX] at h1
    have h2 := Subgroup.card_le_of_le N0_le
    have h3 := card_N_le
    omega
  · rw [← N0_eq, Nat.le_antisymm (N0_eq ▸ card_N_le) card_N0_ge]
    norm_num

theorem cl_spec : ∀ u, 0 < u → u < 16 → CL.getD u 0 < 87 ∧ (EM.getD 0 0).testBit (CL.getD u 0) = true ∧
    ∀ b ∈ B, pg 12 4095 (TF RN) (ivA 12 4095 TF vu vv ((0 :: EL 5).getD u 0) b) =
      ivA 12 4095 TF vu vv (CL.getD u 0) (pg 12 4095 (TF RN) b) :=
  clEK_spec cl

theorem EL0_mem {u : Nat} (hu0 : 0 < u) (hu : u < 16) : CL.getD u 0 ∈ EL 0 := by
  have h := (cl_spec u hu0 hu).2.1
  rw [← (fibk (by norm_num : 0 < 8)).1, testBit_maskL] at h
  exact h

theorem conj_r {u : Nat} (hu : u < 16) :
    G.E RN * s u * (G.E RN)⁻¹ ∈ S 0 := by
  rcases Nat.eq_zero_or_pos u with rfl | hu0
  · left
    simp [s]
  obtain ⟨h1, -, h3⟩ := cl_spec u hu0 hu
  right
  refine ⟨CL.getD u 0, EL0_mem hu0 hu, ?_⟩
  rw [eq_mul_inv_iff_mul_eq, s_ne hu0 hu]
  refine eq_of_base ctx checks fun p hp => ?_
  have hp' : p < 3850 := checks.hB p hp
  have hi := lt_of_EL (by norm_num) (SL_mem hu0 hu)
  change act 3850 (Vi _ * G.E RN) p = act 3850 (G.E RN * Vi _) p
  rw [act_mul _ _ hp', act_mul _ _ hp', act_Vi h1 (act_lt _ hp'), act_Vi hi hp',
    ctx.actE _ rnLt _ hp', ctx.actE _ rnLt _ (by rw [← act_Vi hi hp']; exact act_lt _ hp')]
  exact (h3 p hp).symm

theorem eq_S0 (E : Subgroup ↥hsP) (hE : (E : Set ↥hsP) = S 0) :
    E = E5.map (MulAut.conj (G.E RN)).toMonoidHom := by
  have hsub : ((E5.map (MulAut.conj (G.E RN)).toMonoidHom : Subgroup ↥hsP) : Set ↥hsP) ⊆ S 0 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_s hx
    exact conj_r hu
  have hcard : Nat.card (E5.map (MulAut.conj (G.E RN)).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (G.E RN)).injective, card_E5]
  have h16 : ((E5.map (MulAut.conj (G.E RN)).toMonoidHom : Subgroup ↥hsP) : Set ↥hsP).ncard = 16 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h16]; exact S_ncard (by norm_num))
    (S_finite 0)
  exact SetLike.coe_injective (hE.trans heq.symm)

theorem fixc_V {i : Nat} (hi : i < 87) :
    (Finset.univ.filter fun p : Fin 3850 => ((Vi i : ↥hsP) : Equiv.Perm (Fin 3850)) p = p).card =
      (FL i).length := by
  have hFL := FL_spec ctx checks hi
  refine card_eq_length (D := D) hFL.1 hFL.2.1 _ fun p => ?_
  rw [hFL.2.2 p.val p.isLt, act_eq]
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    exact Fin.ext h

theorem fib_S {k : Nat} (hk : k < 8) (h0 : k ≠ 0) (h5 : k ≠ 5) (E : Subgroup ↥hsP)
    (hE : ∀ x ∈ E, x ≠ 1 → ∃ i ∈ EL k, Vi i = x) :
    ∀ l : List ↥hsP, l.Nodup → (∀ x ∈ l, x ∈ E ∧ x ≠ 1) → ∀ c : ℕ,
      (∀ x ∈ l, (Finset.univ.filter fun p : Fin 3850 =>
        ((x : ↥hsP) : Equiv.Perm (Fin 3850)) p = p).card = c) → l.length < 10 := by
  classical
  intro l hnd hl c hc
  rcases l with _ | ⟨x0, l'⟩
  · simp
  choose! ι hι hιx using fun x (hx : x ∈ E ∧ x ≠ 1) => hE x hx.1 hx.2
  have hmem : ∀ x ∈ x0 :: l', ι x ∈ EL k ∧ Vi (ι x) = x := fun x hx => ⟨hι x (hl x hx), hιx x (hl x hx)⟩
  have hnd' : ((x0 :: l').map ι).Nodup := hnd.map_on fun x hx y hy e => by
    rw [← (hmem x hx).2, ← (hmem y hy).2, e]
  have hF : ∀ x ∈ x0 :: l', (FL (ι x)).length = c := by
    intro x hx
    rw [← fixc_V (lt_of_EL hk (hmem x hx).1), (hmem x hx).2]
    exact hc x hx
  have hsub : (x0 :: l').map ι ⊆ (EL k).filter fun y => (FL y).length == (FL (ι x0)).length := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_filter, beq_iff_eq, hF x hx, hF x0 List.mem_cons_self]
    exact ⟨(hmem x hx).1, rfl⟩
  have h1 := (hnd'.subperm hsub).length_le
  have h2 := (fibk hk).2.2.2.2 h0 h5 (ι x0) (hmem x0 List.mem_cons_self).1
  simp only [List.length_map] at h1
  omega

theorem facts : ∃ R : Subgroup ↥hsP, Nat.card R = 512 ∧
    ∃ (E₀ : Subgroup ↥hsP) (Ek : ℕ → Subgroup ↥hsP), CFSG.QuasithinUnique.A5.LocHypD E₀ ∧
    ∀ E : Subgroup ↥hsP, E ≤ R → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E = 16 → (∃ k < 8, E = Ek k) ∧
      ((∀ l : List ↥hsP, l.Nodup → (∀ x ∈ l, x ∈ E ∧ x ≠ 1) → ∀ c : ℕ,
        (∀ x ∈ l, (Finset.univ.filter fun p : Fin 3850 =>
          ((x : ↥hsP) : Equiv.Perm (Fin 3850)) p = p).card = c) → l.length < 10) ∨
      ∃ r : ↥hsP, E = E₀.map (MulAut.conj r).toMonoidHom) := by
  refine ⟨H.R, card_R, E5, fun k => Subgroup.closure (S k), locHypD_E5,
    fun E hER hc hs hcard => ?_⟩
  obtain ⟨j, hj, hE⟩ := classify E hER hc hs hcard
  have hS := eq_S hj E hE hcard
  refine ⟨⟨j, hj, ?_⟩, ?_⟩
  · change E = Subgroup.closure (S j)
    rw [← hS, Subgroup.closure_eq]
  by_cases h0 : j = 0
  · subst h0
    exact Or.inr ⟨G.E RN, eq_S0 E hS⟩
  by_cases h5 : j = 5
  · subst h5
    refine Or.inr ⟨1, ?_⟩
    have e : E = E5 := SetLike.coe_injective hS
    rw [e]
    ext x
    simp
  · exact Or.inl (fib_S hj h0 h5 E hE)

end CFSG.KD.HS4062.F

end
