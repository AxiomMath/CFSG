module

public import Certificates.Kernel.Ru4120.G
public import Certificates.Kernel.Ru4120.One
public import CFSG.Certificates.Kernel.Kc3DfsKSound
public import CFSG.Certificates.Kernel.Kc3E16KSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineDfs
public import Certificates.Kernel.Ru4120.E
public import Certificates.Kernel.Ru4120.I
public import Certificates.Kernel.Ru4120.P
public import Certificates.Kernel.Ru4120.S0
public import Certificates.Kernel.Ru4120.S1
public import Certificates.Kernel.Ru4120.S2
public import Certificates.Kernel.Ru4120.S3

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Ru4120.H

open CFSG.KD.Ru4120 CFSG.KC.Kc3K CFSG.KC.Enum
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.A5.Kc3SporLine
open CFSG.QuasithinUnique.A5.Kc3SporPerm

theorem hB : ∀ p ∈ B, p < 4060 := by decide

theorem el_ok {k : Nat} (hk : k < 16384) :
    elK 12 4095 486 16384 687 TF B gs eu ev ky iv kv tg k = true := by
  have hc : k / 512 < 32 := by omega
  have h := CFSG.KD.Ru4120.E.all (k / 512) hc
  unfold famE at h
  have e : Nat.add (Nat.mul (k / 512) 512) (k % 512) = k := by
    change k / 512 * 512 + k % 512 = k
    omega
  have := List.all_eq_true.1 h (k % 512) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  rwa [e] at this

theorem iv_ok {i : Nat} (hi : i < 687) :
    ivK 12 4095 16384 687 15 TF B eu ev ky kv vu vv rt cj RI FR FL FM i = true := by
  have hc : i / 64 < 11 := by omega
  have h := CFSG.KD.Ru4120.I.all (i / 64) hc
  unfold famI at h
  have e : Nat.add (Nat.mul (i / 64) 64) (i % 64) = i := by
    change i / 64 * 64 + i % 64 = i
    omega
  have := List.all_eq_true.1 h (i % 64) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  rw [e] at this
  simpa [hi] using this

theorem rt_ok {ρ : Nat} (hρ : ρ < 15) : rtK 12 4095 4060 687 TF vu vv RI FR ρ = true :=
  List.all_eq_true.1 famR_ok ρ (List.mem_range.2 hρ)

theorem pn_ok {i : Nat} (hi : i < 687) :
    prK 12 4095 687 TF B ky kv vu vv pr ct FL FM i = true ∧ nbK 687 pr NB NM i = true := by
  have hc : i / 16 < 43 := by omega
  have h := CFSG.KD.Ru4120.P.all (i / 16) hc
  unfold famP at h
  have e : Nat.add (Nat.mul (i / 16) 16) (i % 16) = i := by
    change i / 16 * 16 + i % 16 = i
    omega
  have := List.all_eq_true.1 h (i % 16) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  rw [e] at this
  simpa [hi] using this

theorem famS_ok {c : Nat} (hc : c < 43) : famS c = true := by
  by_cases h0 : c < 11
  · exact S0.all c h0
  have e : ∀ q, q ≤ c → Nat.add q (c - q) = c := fun q hq => by
    change q + (c - q) = c
    omega
  by_cases h1 : c < 22
  · have hc' : c - 11 < 11 := by omega
    have := S1.all (c - 11) hc'
    unfold famS1 at this
    rwa [e 11 (by omega)] at this
  by_cases h2 : c < 33
  · have hc' : c - 22 < 11 := by omega
    have := S2.all (c - 22) hc'
    unfold famS2 at this
    rwa [e 22 (by omega)] at this
  · have hc' : c - 33 < 10 := by omega
    have := S3.all (c - 33) hc'
    unfold famS3 at this
    rwa [e 33 (by omega)] at this

theorem nb_spec {i : Nat} (hi : i < 687) (j : Nat) : j ∈ NB i ↔ j < 687 ∧ pr i j < 687 := by
  rw [(nbK_spec (pn_ok hi).2).1, List.mem_filter, List.mem_range, decide_eq_true_eq]

theorem dfs_ok : dfsB 687 pr ct NB = true := by
  refine dfsB_of_dfsKI (NM := NM) (fun i hi j hj => ((nb_spec hi j).1 hj).1)
    (fun x hx y hy hp => ?_) (fun i hi => ?_)
  · rw [(nbK_spec (pn_ok hx).2).2, testBit_maskL]
    exact (nb_spec hx y).2 ⟨hy, hp⟩
  · have h := famS_ok (c := i / 16) (by omega)
    unfold famS at h
    refine dfsKR_spec h i ?_ ?_
    · change i / 16 * 16 ≤ i
      omega
    · change i < i / 16 * 16 + min 16 (687 - i / 16 * 16)
      omega

section Prefix

variable {Γ : Type} [Group Γ]

theorem getD_foldl_eltStep : ∀ (l : List (Nat × Nat)) (acc : Array Γ) {i : Nat}, i < acc.size →
    (l.foldl eltStep acc).getD i 1 = acc.getD i 1
  | [], _, _, _ => rfl
  | p :: l, acc, i, hi => by
    rw [List.foldl_cons, getD_foldl_eltStep l _ (by unfold eltStep; simp; omega)]
    exact getD_push_lt acc _ 1 hi

theorem size_foldl_eltStep : ∀ (l : List (Nat × Nat)) (acc : Array Γ),
    (l.foldl eltStep acc).size = acc.size + l.length
  | [], _ => rfl
  | p :: l, acc => by
    rw [List.foldl_cons, size_foldl_eltStep l, List.length_cons]
    simp [eltStep]
    omega

theorem slpElts_ruProg (a b : Γ) {j : Nat} (hj : j < ruProg.length + 2) :
    (slpElts a b ruProg).getD j 1 = G.E a b j := by
  unfold G.E slpElts progX
  rw [List.foldl_append, getD_foldl_eltStep (pairsOf XP) (ruProg.foldl eltStep #[a, b])
    (by rw [size_foldl_eltStep]; simp; omega)]

end Prefix

section Group

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 4060)]

structure Ctx (a b : Γ) : Prop where
  ta : (tab 4060 a).toArray = ruTa
  tb : (tab 4060 b).toArray = ruTb
  base : ∀ g : Γ, (∀ p ∈ B, act 4060 g p = p) → g = 1

@[expose] noncomputable def X (a b : Γ) (k : Nat) : Γ := G.E a b (eu k) * G.E a b (ev k)

@[expose] noncomputable def V (a b : Γ) (i : Nat) : Γ := X a b (kv i)

@[expose] noncomputable def RX (a b : Γ) : Subgroup Γ := Subgroup.closure {y | y ∈ gs.map (G.E a b)}

variable {a b : Γ}

theorem act_inv_act (g : Γ) {p : Nat} (hp : p < 4060) : act 4060 g⁻¹ (act 4060 g p) = p := by
  rw [← act_mul _ _ hp, inv_mul_cancel, act_one hp]

theorem act_act_inv (g : Γ) {p : Nat} (hp : p < 4060) : act 4060 g (act 4060 g⁻¹ p) = p := by
  rw [← act_mul _ _ hp, mul_inv_cancel, act_one hp]

theorem eq_of_base (h : Ctx a b) {g g' : Γ} (hg : ∀ p ∈ B, act 4060 g p = act 4060 g' p) :
    g = g' := by
  have h1 := h.base (g⁻¹ * g') fun p hp => by
    rw [act_mul _ _ (hB p hp), ← hg p hp, act_inv_act _ (hB p hp)]
  exact inv_mul_eq_one.1 h1

theorem eq_of_key (h : Ctx a b) {g g' : Γ}
    (hk : packL 12 (B.map (act 4060 g)) = packL 12 (B.map (act 4060 g'))) : g = g' := by
  refine eq_of_base h (eq_of_packL (fun p hp => ?_) (fun p hp => ?_) hk)
  · exact lt_trans (act_lt g (hB p hp)) (by norm_num)
  · exact lt_trans (act_lt g' (hB p hp)) (by norm_num)

theorem key_map {f g : Nat → Nat} (hfg : ∀ p ∈ B, f p = g p) :
    packL 12 (B.map f) = packL 12 (B.map g) := by
  rw [List.map_congr_left hfg]

theorem act_E (h : Ctx a b) {j : Nat} (hj : j < 486) {p : Nat} (hp : p < 4060) :
    act 4060 (G.E a b j) p = pg 12 4095 (TF j) p := G.act_node h.ta h.tb hj hp

theorem act_X (h : Ctx a b) {k : Nat} (hk : k < 16384) {p : Nat} (hp : p < 4060) :
    act 4060 (X a b k) p = exK 12 4095 TF (eu k) (ev k) p := by
  obtain ⟨hu, hv, -⟩ := elK_spec (el_ok hk)
  have h1 := act_lt (G.E a b (ev k)) hp
  unfold X exK
  rw [act_mul _ _ hp, act_E h hu h1, act_E h hv hp]

theorem key_X (h : Ctx a b) {k : Nat} (hk : k < 16384) :
    ky k = packL 12 (B.map (act 4060 (X a b k))) := by
  rw [(elK_spec (el_ok hk)).2.2.1]
  exact key_map fun p hp => (act_X h hk (hB p hp)).symm

theorem X_tg (h : Ctx a b) {k : Nat} (hk : k < 16384) {c : Nat} (hc : c < 3) :
    tg c k < 16384 ∧ X a b (tg c k) = G.E a b (gs.getD c 0) * X a b k := by
  obtain ⟨-, -, -, ht, -⟩ := elK_spec (el_ok hk)
  obtain ⟨hlt, hkey⟩ := ht c hc
  refine ⟨hlt, eq_of_key h ?_⟩
  rw [← key_X h hlt, hkey]
  have hg : gs.getD c 0 < 486 := by interval_cases c <;> decide
  refine key_map fun p hp => ?_
  rw [act_mul _ _ (hB p hp), act_E h hg (act_lt _ (hB p hp)), act_X h hk (hB p hp)]

theorem X_one (h : Ctx a b) : X a b 16 = 1 := by
  refine eq_of_base h fun p hp => ?_
  rw [act_X h (by norm_num) (hB p hp), act_one (hB p hp)]
  exact beq_iff_eq.1 (List.all_eq_true.1 one p hp)

theorem mem_X [Finite Γ] (h : Ctx a b) {g : Γ} (hg : g ∈ RX a b) : ∃ k < 16384, X a b k = g := by
  have hstep : ∀ s ∈ {y | y ∈ gs.map (G.E a b)}, ∀ k < 16384, ∃ k' < 16384,
      X a b k' = s * X a b k := by
    intro s hs k hk
    rw [Set.mem_setOf_eq] at hs
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hs
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hg
    have hc3 : c < 3 := hc
    obtain ⟨h1, h2⟩ := X_tg h hk hc3
    rw [List.getD_eq_getElem _ _ hc] at h2
    exact ⟨_, h1, h2⟩
  refine Subgroup.closure_induction_left (p := fun g _ => ∃ k < 16384, X a b k = g)
    ⟨16, by norm_num, X_one h⟩ ?_ ?_ hg
  · rintro s hs y - ⟨k, hk, rfl⟩
    exact hstep s hs k hk
  · rintro s hs y - ⟨k, hk, rfl⟩
    have hpow : ∀ n : Nat, ∃ k' < 16384, X a b k' = s ^ n * X a b k := by
      intro n
      induction n with
      | zero => exact ⟨k, hk, by rw [pow_zero, one_mul]⟩
      | succ n ih =>
        obtain ⟨k1, hk1, e1⟩ := ih
        obtain ⟨k2, hk2, e2⟩ := hstep s hs k1 hk1
        exact ⟨k2, hk2, by rw [e2, e1, pow_succ', mul_assoc]⟩
    have hinv : s⁻¹ = s ^ (orderOf s - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [pow_sub_one_mul (orderOf_pos s).ne', pow_orderOf_eq_one]
    rw [hinv]
    exact hpow _

theorem V_spec {i : Nat} (hi : i < 687) : kv i < 16384 ∧ vu i = eu (kv i) ∧ vv i = ev (kv i) := by
  obtain ⟨h1, h2, h3, -⟩ := ivK_spec (iv_ok hi)
  exact ⟨h1, h2, h3⟩

theorem act_V (h : Ctx a b) {i : Nat} (hi : i < 687) {p : Nat} (hp : p < 4060) :
    act 4060 (V a b i) p = exK 12 4095 TF (vu i) (vv i) p := by
  obtain ⟨h1, h2, h3⟩ := V_spec hi
  rw [h2, h3]
  exact act_X h h1 hp

theorem key_V (h : Ctx a b) {i : Nat} (hi : i < 687) :
    ky (kv i) = packL 12 (B.map (act 4060 (V a b i))) := key_X h (V_spec hi).1

theorem key_lt {i j : Nat} (hij : i < j) (hj : j < 687) : ky (kv i) < ky (kv j) := by
  induction j, hij using Nat.le_induction with
  | base => exact (ivK_spec (iv_ok (by omega : i < 687))).2.2.2.1 hj
  | succ n hn ih =>
    exact lt_trans (ih (by omega)) ((ivK_spec (iv_ok (by omega : n < 687))).2.2.2.1 hj)

theorem V_inj (h : Ctx a b) {i : Nat} (hi : i < 687) {j : Nat} (hj : j < 687)
    (he : V a b i = V a b j) : i = j := by
  have e : ky (kv i) = ky (kv j) := by rw [key_V h hi, key_V h hj, he]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd e (key_lt hij hj).ne
  · exact hij
  · exact absurd e (key_lt hij hi).ne'

theorem V_list [Finite Γ] (h : Ctx a b) {x : Γ} (hx : x ∈ RX a b) (hxx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ i < 687, V a b i = x := by
  obtain ⟨k, hk, rfl⟩ := mem_X h hx
  have hsq : ∀ p ∈ B, exK 12 4095 TF (eu k) (ev k) (exK 12 4095 TF (eu k) (ev k) p) = p := by
    intro p hp
    have e : act 4060 (X a b k * X a b k) p = act 4060 (1 : Γ) p := by rw [hxx]
    rw [act_mul _ _ (hB p hp), act_X h hk (act_lt _ (hB p hp)), act_X h hk (hB p hp),
      act_one (hB p hp)] at e
    exact e
  have hmv : ∃ p ∈ B, exK 12 4095 TF (eu k) (ev k) p ≠ p := by
    by_contra! hn
    exact hx1 (h.base _ fun p hp => by rw [act_X h hk (hB p hp)]; exact hn p hp)
  obtain ⟨hlt, he⟩ := (elK_spec (el_ok hk)).2.2.2.2 hsq hmv
  exact ⟨iv k, hlt, by unfold V; rw [he]⟩

theorem V_pr_lt (h : Ctx a b) {i j : Nat} (hij : i < j) (hj : j < 687)
    (hc : V a b i * V a b j = V a b j * V a b i) :
    pr i j < 687 ∧ V a b (pr i j) = V a b i * V a b j := by
  have hi : i < 687 := by omega
  obtain ⟨-, hr⟩ := prK_spec (pn_ok hi).1 j hj
  obtain ⟨hlt, hge⟩ := hr hij
  have hp : pr i j < 687 := by
    by_contra hn
    obtain ⟨p, hp, hne⟩ := hge hn
    apply hne
    have e : act 4060 (V a b i * V a b j) p = act 4060 (V a b j * V a b i) p := by rw [hc]
    rw [act_mul _ _ (hB p hp), act_mul _ _ (hB p hp), act_V h hi (act_lt _ (hB p hp)),
      act_V h hj (hB p hp), act_V h hj (act_lt _ (hB p hp)), act_V h hi (hB p hp)] at e
    exact e
  refine ⟨hp, eq_of_key h ?_⟩
  rw [← key_V h hp, (hlt hp).1]
  refine key_map fun p hp => ?_
  rw [act_mul _ _ (hB p hp), act_V h hi (act_lt _ (hB p hp)), act_V h hj (hB p hp)]

theorem V_pr (h : Ctx a b) {i : Nat} (hi : i < 687) {j : Nat} (hj : j < 687) (hij : i ≠ j)
    (hc : V a b i * V a b j = V a b j * V a b i) :
    pr i j < 687 ∧ V a b (pr i j) = V a b i * V a b j := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact V_pr_lt h hlt hj hc
  · have e := ((prK_spec (pn_ok hi).1 j hj).1)
    obtain ⟨h1, h2⟩ := V_pr_lt h hlt hi hc.symm
    rw [e, h2, hc]
    exact ⟨h1, rfl⟩

theorem card_eq_length {l : List Nat} (hnd : l.Nodup) (hlt : ∀ p ∈ l, p < 4060)
    (P : Fin 4060 → Prop) [DecidablePred P] (hP : ∀ p : Fin 4060, P p ↔ p.val ∈ l) :
    (Finset.univ.filter P).card = l.length := by
  rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    List.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hP p).1 hp
  · intro hx
    exact ⟨⟨x, hlt x hx⟩, (hP _).2 hx, rfl⟩

theorem FR_spec (h : Ctx a b) {ρ : Nat} (hρ : ρ < 15) :
    RI ρ < 687 ∧ (FR ρ).Nodup ∧ (∀ p ∈ FR ρ, p < 4060) ∧
      ∀ p < 4060, p ∈ FR ρ ↔ act 4060 (V a b (RI ρ)) p = p := by
  obtain ⟨hr, hs, hf, hc⟩ := rtK_spec (rt_ok hρ)
  have hnd : (FR ρ).Nodup := hs.imp (fun h => h.ne)
  let F := (List.range 4060).filter fun p => exK 12 4095 TF (vu (RI ρ)) (vv (RI ρ)) p == p
  have hsub : (FR ρ).toFinset ⊆ F.toFinset := by
    intro p hp
    rw [List.mem_toFinset] at hp ⊢
    obtain ⟨h1, h2⟩ := hf p hp
    exact List.mem_filter.2 ⟨List.mem_range.2 h1, beq_iff_eq.2 h2⟩
  have heq : (FR ρ).toFinset = F.toFinset := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup
      ((List.nodup_range).filter _), hc])
  refine ⟨hr, hnd, fun p hp => (hf p hp).1, fun p hp => ?_⟩
  rw [act_V h hr hp, ← List.mem_toFinset, heq, List.mem_toFinset, List.mem_filter, List.mem_range,
    beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

theorem FL_spec (h : Ctx a b) {i : Nat} (hi : i < 687) :
    (FL i).Nodup ∧ (∀ p ∈ FL i, p < 4060) ∧ ∀ p < 4060, p ∈ FL i ↔ act 4060 (V a b i) p = p := by
  obtain ⟨-, -, -, -, hrt, -, hcj, hconj, hFL, -⟩ := ivK_spec (iv_ok hi)
  obtain ⟨hr, hnd, hlt, hfix⟩ := FR_spec h hrt
  set y := X a b (cj i)
  set r := RI (rt i)
  have hy : ∀ p < 4060, exK 12 4095 TF (eu (cj i)) (ev (cj i)) p = act 4060 y p :=
    fun p hp => (act_X h hcj hp).symm
  have hVi : V a b i = y * V a b r * y⁻¹ := by
    have e : V a b i * y = y * V a b r := eq_of_base h fun p hp => by
      have hq : exK 12 4095 TF (vu r) (vv r) p < 4060 := by
        rw [← act_V h hr (hB p hp)]
        exact act_lt _ (hB p hp)
      have hq' : exK 12 4095 TF (eu (cj i)) (ev (cj i)) p < 4060 := by
        rw [hy p (hB p hp)]
        exact act_lt _ (hB p hp)
      rw [act_mul _ _ (hB p hp), act_mul _ _ (hB p hp), ← hy p (hB p hp), act_V h hi hq',
        act_V h hr (hB p hp), ← hy _ hq]
      exact hconj p hp
    rw [← e, mul_inv_cancel_right]
  have hFL' : FL i = (FR (rt i)).map (act 4060 y) := by
    rw [hFL]
    exact List.map_congr_left fun p hp => hy p (hlt p hp)
  refine ⟨?_, ?_, fun p hp => ?_⟩
  · rw [hFL']
    refine hnd.map_on fun p hp q hq e => ?_
    rw [← act_inv_act y (hlt p hp), e, act_inv_act y (hlt q hq)]
  · rw [hFL']
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact act_lt y (hlt q hq)
  · have hp' := act_lt y⁻¹ hp
    rw [hFL', hVi, act_mul _ _ hp, act_mul _ _ (act_lt _ hp)]
    constructor
    · intro hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
      rw [act_inv_act y (hlt q hq), (hfix q (hlt q hq)).1 hq]
    · intro he
      have e2 : act 4060 (V a b r) (act 4060 y⁻¹ p) = act 4060 y⁻¹ p := by
        have := congrArg (act 4060 y⁻¹) he
        rwa [act_inv_act y (act_lt _ hp')] at this
      exact List.mem_map.2 ⟨_, (hfix _ hp').2 e2, act_act_inv y hp⟩

theorem fixc_symm (x y : Γ) : fixc (Fin 4060) x y = fixc (Fin 4060) y x := by
  unfold fixc
  simp only [and_comm]

theorem ct_lt (h : Ctx a b) {i j : Nat} (hij : i < j) (hj : j < 687) (hp : pr i j < 687) :
    ct i j = fixc (Fin 4060) (V a b i) (V a b j) := by
  have hi : i < 687 := by omega
  obtain ⟨-, hr⟩ := prK_spec (pn_ok hi).1 j hj
  obtain ⟨-, -, hct⟩ := (hr hij).1 hp
  obtain ⟨-, -, -, -, -, -, -, -, -, hFM⟩ := ivK_spec (iv_ok hj)
  obtain ⟨hnd, hlt, hfix⟩ := FL_spec h hi
  obtain ⟨-, -, hfixj⟩ := FL_spec h hj
  rw [hct, cntIn_eq, fixc]
  symm
  refine card_eq_length (hnd.filter _) (fun p hp => hlt p (List.mem_of_mem_filter hp)) _
    fun p => ?_
  rw [List.mem_filter, hFM, testBit_maskL, hfix p p.isLt, hfixj p p.isLt, act_eq, act_eq,
    Fin.val_eq_val, Fin.val_eq_val]

theorem ct_spec (h : Ctx a b) {i : Nat} (hi : i < 687) {j : Nat} (hj : j < 687) (hij : i ≠ j)
    (hp : pr i j < 687) : ct i j = fixc (Fin 4060) (V a b i) (V a b j) := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact ct_lt h hlt hj hp
  · have e := (prK_spec (pn_ok hi).1 j hj).1
    rw [e] at hp
    obtain ⟨-, hr⟩ := prK_spec (pn_ok hj).1 i hi
    obtain ⟨-, hct, -⟩ := (hr hlt).1 hp
    rw [← hct, ct_lt h hlt hi hp, fixc_symm]

theorem hall [Finite Γ] (h : Ctx a b) :
    ∀ E : Subgroup Γ, E ≤ RX a b → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E = 16 → ¬ PairFibersAllowed (Fin 4060) E :=
  hall_of_dfs_of_specs (Fin 4060) 687 (V a b) pr ct NB
    (fun x hx hxx hx1 => V_list h hx hxx hx1)
    (fun i hi j hj he => V_inj h hi hj he)
    (fun i hi j hj hij hc => V_pr h hi hj hij hc)
    (fun i hi j hj hij hc => (nb_spec hi j).2 ⟨hj, (V_pr h hi hj hij hc).1⟩)
    (fun i hi j hj hij hp => ct_spec h hi hj hij hp) dfs_ok

end Group

end CFSG.KD.Ru4120.H

end
