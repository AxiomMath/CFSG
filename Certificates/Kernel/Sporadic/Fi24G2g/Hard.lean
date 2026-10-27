
module

public import Certificates.Kernel.Sporadic.Fi24G2g.Fix
public import Certificates.Kernel.Sporadic.Fi24G2e.Leaves

public section

namespace CertificateChecks.KernelFi24G2g

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix CertificateChecks.KernelFi24Orb
  CertificateChecks.KernelFi24G2e TauCeti TauCeti.Sporadic CFSG.KC.Fi24FixK CFSG.KC.Fi24FixS

open CFSG.Sporadic.Fi24 (R cls D24)
open CFSG.KD.Fi24Orb (NM NI)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction

@[expose] def buildE {G : Type*} [Group G] (L : ℕ → G) (node : List ℕ) : ℕ → List G
  | 0 => (List.range 6).map L
  | t + 1 => buildE L node t ++
      [⁅((buildE L node t).getD (node.getD (2 * t + 1) 0) 1)⁻¹,
        ((buildE L node t).getD (node.getD (2 * t) 0) 1)⁻¹⁆]

@[expose] def buildD (node : List ℕ) : ℕ → List ℕ
  | 0 => List.replicate 6 0
  | t + 1 => buildD node t ++
      [min ((buildD node t).getD (node.getD (2 * t + 1) 0) 0)
        ((buildD node t).getD (node.getD (2 * t) 0) 0) + 1]

theorem buildE_length {G : Type*} [Group G] (L : ℕ → G) (node : List ℕ) :
    ∀ t, (buildE L node t).length = 6 + t
  | 0 => by simp [buildE]
  | t + 1 => by rw [buildE, List.length_append, buildE_length L node t]; simp; omega

theorem buildD_length (node : List ℕ) : ∀ t, (buildD node t).length = 6 + t
  | 0 => by simp [buildD]
  | t + 1 => by rw [buildD, List.length_append, buildD_length node t]; simp; omega

theorem buildE_getD {G : Type*} [Group G] (L : ℕ → G) (node : List ℕ) {t k : ℕ} (hk : k < 6 + t) :
    (buildE L node (t + 1)).getD k 1 = (buildE L node t).getD k 1 := by
  rw [buildE, List.getD_append _ _ _ _ (by rw [buildE_length]; exact hk)]

theorem buildD_getD (node : List ℕ) {t k : ℕ} (hk : k < 6 + t) :
    (buildD node (t + 1)).getD k 0 = (buildD node t).getD k 0 := by
  rw [buildD, List.getD_append _ _ _ _ (by rw [buildD_length]; exact hk)]

theorem buildE_stable {G : Type*} [Group G] (L : ℕ → G) (node : List ℕ) {t k : ℕ} (hk : k < 6 + t) :
    ∀ s, (buildE L node (t + s)).getD k 1 = (buildE L node t).getD k 1
  | 0 => rfl
  | s + 1 => by
    rw [← Nat.add_assoc, buildE_getD L node (by omega), buildE_stable L node hk s]

theorem buildD_stable (node : List ℕ) {t k : ℕ} (hk : k < 6 + t) :
    ∀ s, (buildD node (t + s)).getD k 0 = (buildD node t).getD k 0
  | 0 => rfl
  | s + 1 => by
    rw [← Nat.add_assoc, buildD_getD node (by omega), buildD_stable node hk s]

@[expose] def nodeE {G : Type*} [Group G] (L : ℕ → G) (node : List ℕ) (k : ℕ) : G :=
  (buildE L node 15).getD k 1

@[expose] def nodeD (node : List ℕ) (k : ℕ) : ℕ := (buildD node 15).getD k 0

theorem nodeE_leaf {G : Type*} [Group G] (L : ℕ → G) (node : List ℕ) {j : ℕ} (hj : j < 6) :
    nodeE L node j = L j := by
  unfold nodeE
  rw [show (15 : ℕ) = 0 + 15 from rfl, buildE_stable L node (t := 0) (by omega) 15]
  simp [buildE, List.getD_eq_getElem?_getD, hj]

theorem nodeE_node {G : Type*} [Group G] (L : ℕ → G) (node : List ℕ) {t : ℕ} (ht : t < 15)
    (ha : node.getD (2 * t) 0 < t + 6) (hb : node.getD (2 * t + 1) 0 < t + 6) :
    nodeE L node (t + 6) = ⁅(nodeE L node (node.getD (2 * t + 1) 0))⁻¹,
      (nodeE L node (node.getD (2 * t) 0))⁻¹⁆ := by
  unfold nodeE
  obtain ⟨s, hs⟩ : ∃ s, 15 = (t + 1) + s := ⟨15 - (t + 1), by omega⟩
  have low : ∀ k, k < t + 6 →
      (buildE L node 15).getD k 1 = (buildE L node t).getD k 1 := fun k hk => by
    rw [hs, buildE_stable L node (t := t + 1) (k := k) (by omega) s, buildE_getD L node (by omega)]
  have top : (buildE L node 15).getD (t + 6) 1 = (buildE L node (t + 1)).getD (t + 6) 1 := by
    rw [hs]
    exact buildE_stable L node (t := t + 1) (k := t + 6) (by omega) s
  have e3 : (buildE L node (t + 1)).getD (t + 6) 1 =
      ⁅((buildE L node t).getD (node.getD (2 * t + 1) 0) 1)⁻¹,
        ((buildE L node t).getD (node.getD (2 * t) 0) 1)⁻¹⁆ := by
    rw [buildE, List.getD_append_right _ _ _ _ (by rw [buildE_length]; omega), buildE_length,
      show t + 6 - (6 + t) = 0 by omega]
    rfl
  rw [top, e3, low _ ha, low _ hb]

theorem nodeD_leaf (node : List ℕ) {j : ℕ} (hj : j < 6) : nodeD node j = 0 := by
  unfold nodeD
  rw [show (15 : ℕ) = 0 + 15 from rfl, buildD_stable node (t := 0) (by omega) 15]
  simp only [buildD, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj,
    Option.getD_some]

theorem nodeD_node (node : List ℕ) {t : ℕ} (ht : t < 15)
    (ha : node.getD (2 * t) 0 < t + 6) (hb : node.getD (2 * t + 1) 0 < t + 6) :
    nodeD node (t + 6) = min (nodeD node (node.getD (2 * t + 1) 0))
      (nodeD node (node.getD (2 * t) 0)) + 1 := by
  unfold nodeD
  obtain ⟨s, hs⟩ : ∃ s, 15 = (t + 1) + s := ⟨15 - (t + 1), by omega⟩
  have low : ∀ k, k < t + 6 →
      (buildD node 15).getD k 0 = (buildD node t).getD k 0 := fun k hk => by
    rw [hs, buildD_stable node (t := t + 1) (k := k) (by omega) s, buildD_getD node (by omega)]
  have top : (buildD node 15).getD (t + 6) 0 = (buildD node (t + 1)).getD (t + 6) 0 := by
    rw [hs]
    exact buildD_stable node (t := t + 1) (k := t + 6) (by omega) s
  have e3 : (buildD node (t + 1)).getD (t + 6) 0 =
      min ((buildD node t).getD (node.getD (2 * t + 1) 0) 0)
        ((buildD node t).getD (node.getD (2 * t) 0) 0) + 1 := by
    rw [buildD, List.getD_append_right _ _ _ _ (by rw [buildD_length]; omega), buildD_length,
      show t + 6 - (6 + t) = 0 by omega]
    rfl
  rw [top, e3, low _ ha, low _ hb]

attribute [local irreducible] nodeE nodeD

theorem nodeE_mem {G : Type*} [Group G] (L : ℕ → G) (node : List ℕ)
    (hch : ∀ t < 15, node.getD (2 * t) 0 < t + 6 ∧ node.getD (2 * t + 1) 0 < t + 6) :
    ∀ k < 21, nodeE L node k ∈ derivedSeries G (nodeD node k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h6 : k < 6
    · rw [nodeD_leaf node h6, derivedSeries_zero]
      exact Subgroup.mem_top _
    · obtain ⟨t, rfl⟩ : ∃ t, k = t + 6 := ⟨k - 6, by omega⟩
      obtain ⟨ha, hb⟩ := hch t (by omega)
      rw [nodeE_node L node (by omega) ha hb, nodeD_node node (by omega) ha hb,
        derivedSeries_succ]
      have h1 := ih (node.getD (2 * t + 1) 0) (by omega) (by omega)
      have h2 := ih (node.getD (2 * t) 0) (by omega) (by omega)
      have m1 : (nodeE L node (node.getD (2 * t + 1) 0))⁻¹ ∈ derivedSeries G
          (min (nodeD node (node.getD (2 * t + 1) 0)) (nodeD node (node.getD (2 * t) 0))) :=
        derivedSeries_antitone G (min_le_left _ _) (Subgroup.inv_mem _ h1)
      have m2 : (nodeE L node (node.getD (2 * t) 0))⁻¹ ∈ derivedSeries G
          (min (nodeD node (node.getD (2 * t + 1) 0)) (nodeD node (node.getD (2 * t) 0))) :=
        derivedSeries_antitone G (min_le_right _ _) (Subgroup.inv_mem _ h2)
      exact Subgroup.commutator_mem_commutator m1 m2

theorem nodeE_act {G X : Type*} [Group G] [MulAction G X] (L : ℕ → G) (node : List ℕ) (n : ℕ)
    (F : ℕ → X) (TB TI : ℕ → ℕ → ℕ)
    (hch : ∀ t < 15, node.getD (2 * t) 0 < t + 6 ∧ node.getD (2 * t + 1) 0 < t + 6)
    (hleaf : ∀ j < 6, ∀ i < n, TB j i < n ∧ L j • F i = F (TB j i))
    (hinv : ∀ k < 21, ∀ i < n, TI k i < n ∧ TB k (TI k i) = i)
    (hnode : ∀ t < 15, ∀ i < n, TB (t + 6) i = TI (node.getD (2 * t + 1) 0)
      (TI (node.getD (2 * t) 0) (TB (node.getD (2 * t + 1) 0) (TB (node.getD (2 * t) 0) i)))) :
    ∀ k < 21, ∀ i < n, TB k i < n ∧ nodeE L node k • F i = F (TB k i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hi
    by_cases h6 : k < 6
    · rw [nodeE_leaf L node h6]
      exact hleaf k h6 i hi
    · obtain ⟨t, rfl⟩ : ∃ t, k = t + 6 := ⟨k - 6, by omega⟩
      obtain ⟨ha, hb⟩ := hch t (by omega)
      set a := node.getD (2 * t) 0
      set b := node.getD (2 * t + 1) 0
      have hA := ih a (by omega) (by omega)
      have hB := ih b (by omega) (by omega)
      have invA : ∀ i < n, (nodeE L node a)⁻¹ • F i = F (TI a i) ∧ TI a i < n := by
        intro i hi
        obtain ⟨h1, h2⟩ := hinv a (by omega) i hi
        refine ⟨?_, h1⟩
        rw [inv_smul_eq_iff, (hA (TI a i) h1).2, h2]
      have invB : ∀ i < n, (nodeE L node b)⁻¹ • F i = F (TI b i) ∧ TI b i < n := by
        intro i hi
        obtain ⟨h1, h2⟩ := hinv b (by omega) i hi
        refine ⟨?_, h1⟩
        rw [inv_smul_eq_iff, (hB (TI b i) h1).2, h2]
      have e1 := hA i hi
      have e2 := hB _ e1.1
      have e3 := invA _ e2.1
      have e4 := invB _ e3.2
      refine ⟨by rw [hnode t (by omega) i hi]; exact e4.2, ?_⟩
      rw [nodeE_node L node (by omega) ha hb, commutatorElement_def, inv_inv, inv_inv, mul_smul,
        mul_smul, mul_smul, e1.2, e2.2, e3.1, e4.1, hnode t (by omega) i hi]

theorem brayWord_lt {w g : List ℕ} (hw : ∀ x ∈ w, x < 12) (hg : ∀ x ∈ g, x < 12) (e : ℕ)
    (odd : Bool) : ∀ x ∈ CFSG.KC.Fi24G2e.brayWord w g e odd, x < 12 := by
  intro x hx
  unfold CFSG.KC.Fi24G2e.brayWord at hx
  rcases List.mem_append.1 hx with h | h
  · split at h
    · exact hg x h
    · exact absurd h List.not_mem_nil
  · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 h
    rw [(List.eq_of_mem_replicate hl)] at hxl
    unfold CFSG.KC.Fi24G2e.zWord at hxl
    simp only [List.mem_append, List.mem_reverse] at hxl
    rcases hxl with ((h | h) | h) | h
    · exact hw x h
    · exact hg x h
    · exact hw x h
    · exact hg x h

theorem strict_inj {F : ℕ → ℕ} {n : ℕ} (h : ∀ j, j + 1 < n → F j < F (j + 1)) :
    ∀ i < n, ∀ j < n, F i = F j → i = j := by
  have mono : ∀ i j, i < j → j < n → F i < F j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact (ih h (by omega)).trans (hfun j (by omega))
      · rw [h]; exact hfun j (by omega)
  intro i hi j hj e
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd e (mono i j h hj).ne
  · exact h
  · exact absurd e (mono j i h hi).ne'
where hfun := h

section Bind

@[expose] noncomputable def pkT (r : ℕ) : Fin 306936 :=
  if h : r < 306936 then pk h else ⟨0, by norm_num⟩

theorem pkT_eq {r : ℕ} (h : r < 306936) : pkT r = pk h := dif_pos h

theorem card_fixed_pts2 (r W : R) :
    Nat.card {x : D24 // r * x * r⁻¹ = x ∧ ∀ _i : Fin 1, W * x * W⁻¹ = x} =
      Nat.card {k : Fin 306936 // r • k = k ∧ W • k = k} := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv CFSG.Sporadic.Fi24.clsEquiv fun k => ?_)
  rw [CFSG.Sporadic.Fi24.clsEquiv_apply, ← CFSG.Sporadic.Fi24.cls_smul_R,
    ← CFSG.Sporadic.Fi24.cls_smul_R, forall_const]
  exact and_congr ⟨fun h => by rw [h], fun h => CFSG.Sporadic.Fi24.cls_injective h⟩
    ⟨fun h => by rw [h], fun h => CFSG.Sporadic.Fi24.cls_injective h⟩

variable (hP : PtRank)
include hP

theorem hard_of {w own : List ℕ} {n m : ℕ} {FL : ℕ → ℕ} {LW : ℕ → List ℕ} {TB TI : ℕ → ℕ → ℕ}
    {node : List ℕ}
    (hprod : ρ (wp w) = (own.map fun o => cls (pkT o)).prod)
    (hpair : (own.map fun o => cls (pkT o)).Pairwise Commute)
    (hown : ∀ o ∈ own, o < 306936)
    (hfix : ∀ k : Fin 306936, ρ (wp w) • k = k ↔ ∃ i < n, FL i = NM k)
    (hFL : ∀ i < n, FL i < 306936) (hinj : ∀ i < n, ∀ j < n, FL i = FL j → i = j)
    (hLW : ∀ j < 6, ∀ g ∈ LW j, g < 12)
    (hleaf : ∀ j < 6, ∀ i < n, TB j i < n ∧ walk CFSG.KD.Fi24Fix.TG (LW j) (FL i) = FL (TB j i))
    (hperm : ∀ j < 6, (own.map (walk CFSG.KD.Fi24Fix.TG (LW j))).Perm own)
    (hinv : ∀ k < 21, ∀ i < n, TI k i < n ∧ TB k (TI k i) = i)
    (hnode : ∀ t < 15, ∀ i < n, TB (t + 6) i = TI (node.getD (2 * t + 1) 0)
      (TI (node.getD (2 * t) 0) (TB (node.getD (2 * t + 1) 0) (TB (node.getD (2 * t) 0) i))))
    (hch : ∀ t < 15, node.getD (2 * t) 0 < t + 6 ∧ node.getD (2 * t + 1) 0 < t + 6)
    (hdep : 4 ≤ nodeD node 20)
    (hcnt : ((Finset.range n).filter fun i => TB 20 i = i).card = 2 ^ m) :
    ∃ W : Subgroup.centralizer ({ρ (wp w)} : Set R),
      W ∈ derivedSeries (Subgroup.centralizer ({ρ (wp w)} : Set R)) 4 ∧
      Nat.card {x : D24 // ρ (wp w) * x * (ρ (wp w))⁻¹ = x ∧
        ∀ _i : Fin 1, (W : R) * x * (W : R)⁻¹ = x} = 2 ^ m := by
  set r := ρ (wp w)
  set C := Subgroup.centralizer ({r} : Set R)
  have hL : ∀ j (hj : j < 6) {s : ℕ} (hs : s < 306936),
      (ρ (wp (LW j)))⁻¹ • pk hs = pk (walk_lt (hLW j hj) hs) := fun j hj s hs =>
    smul_pk hP (hLW j hj) hs
  have hLT : ∀ j < 6, ∀ o ∈ own,
      (ρ (wp (LW j)))⁻¹ • pkT o = pkT (walk CFSG.KD.Fi24Fix.TG (LW j) o) := by
    intro j hj o ho
    rw [pkT_eq (hown o ho), hL j hj, pkT_eq]
  have hcomm : ∀ j < 6, (ρ (wp (LW j)))⁻¹ * r = r * (ρ (wp (LW j)))⁻¹ := by
    intro j hj
    have hc : (ρ (wp (LW j)))⁻¹ * r * ((ρ (wp (LW j)))⁻¹)⁻¹ = r := by
      have e1 : (ρ (wp (LW j)))⁻¹ * r * ((ρ (wp (LW j)))⁻¹)⁻¹ =
          (MulAut.conj (ρ (wp (LW j)))⁻¹) r := rfl
      rw [e1, hprod, map_list_prod, List.map_map]
      have e2 : own.map ((MulAut.conj (ρ (wp (LW j)))⁻¹) ∘ fun o => cls (pkT o)) =
          (own.map (walk CFSG.KD.Fi24Fix.TG (LW j))).map fun o => cls (pkT o) := by
        rw [List.map_map]
        refine List.map_congr_left fun o ho => ?_
        change (ρ (wp (LW j)))⁻¹ * cls (pkT o) * ((ρ (wp (LW j)))⁻¹)⁻¹ = _
        rw [← CFSG.Sporadic.Fi24.cls_smul_R, hLT j hj o ho]
        rfl
      rw [e2]
      have hp := ((hperm j hj).map (fun o => cls (pkT o))).symm
      have hq := @List.Perm.prod_eq' R _ _ _ hp hpair
      exact hq.symm
    calc (ρ (wp (LW j)))⁻¹ * r = (ρ (wp (LW j)))⁻¹ * r * ((ρ (wp (LW j)))⁻¹)⁻¹ *
          (ρ (wp (LW j)))⁻¹ := by group
      _ = r * (ρ (wp (LW j)))⁻¹ := by rw [hc]
  let L' : ℕ → C := fun j => if hj : j < 6 then
    ⟨(ρ (wp (LW j)))⁻¹, Subgroup.mem_centralizer_singleton_iff.2 (hcomm j hj)⟩ else 1
  have hleaf' : ∀ j < 6, ∀ i < n, TB j i < n ∧ L' j • pkT (FL i) = pkT (FL (TB j i)) := by
    intro j hj i hi
    refine ⟨(hleaf j hj i hi).1, ?_⟩
    rw [Subgroup.smul_def]
    simp only [L', dif_pos hj]
    rw [pkT_eq (hFL i hi), hL j hj, pkT_eq (hFL _ (hleaf j hj i hi).1)]
    exact pk_congr _ _ (hleaf j hj i hi).2
  have hact := nodeE_act (X := Fin 306936) L' node n (fun i => pkT (FL i)) TB TI hch hleaf' hinv hnode
  refine ⟨nodeE L' node 20, derivedSeries_antitone C hdep (nodeE_mem L' node hch 20 (by norm_num)),
    ?_⟩
  set W := nodeE L' node 20
  have hW : ∀ i < n, (W : R) • pkT (FL i) = pkT (FL (TB 20 i)) := fun i hi => by
    rw [← Subgroup.smul_def]
    exact (hact 20 (by norm_num) i hi).2
  rw [card_fixed_pts2]
  have hpk : ∀ i < n, NM (pkT (FL i)) = FL i := fun i hi => by
    rw [pkT_eq (hFL i hi)]
    exact NM_NI (hFL i hi)
  have hinjT : ∀ i < n, ∀ j < n, pkT (FL i) = pkT (FL j) → i = j := fun i hi j hj e => by
    rw [pkT_eq (hFL i hi), pkT_eq (hFL j hj)] at e
    exact hinj i hi j hj (pk_inj _ _ e)
  let f : {i : Fin n // TB 20 i.val = i.val} → {k : Fin 306936 // r • k = k ∧ (W : R) • k = k} :=
    fun i => ⟨pkT (FL i.1), (hfix _).2 ⟨i.1, i.1.isLt, (hpk _ i.1.isLt).symm⟩, by
      rw [hW _ i.1.isLt, i.2]⟩
  have hb : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (Fin.ext (hinjT _ a.1.isLt _ b.1.isLt
      (congrArg Subtype.val h))), fun k => ?_⟩
    obtain ⟨i, hi, e⟩ := (hfix k.1).1 k.2.1
    have hk : k.1 = pkT (FL i) := by
      rw [pkT_eq (hFL i hi), ← pk_NM k.1]
      exact pk_congr _ _ e.symm
    have hfx : TB 20 i = i := by
      have h2 := k.2.2
      rw [hk, hW i hi] at h2
      exact hinjT _ (hact 20 (by norm_num) i hi).1 _ hi h2
    exact ⟨⟨⟨i, hi⟩, hfx⟩, Subtype.ext hk.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hb), card_fin_filter (fun i => TB 20 i = i) n, hcnt]

end Bind

end CertificateChecks.KernelFi24G2g

end
