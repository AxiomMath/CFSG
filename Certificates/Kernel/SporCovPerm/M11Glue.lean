module

public import Certificates.Kernel.SporCovPerm.M11
public import CFSG.Certificates.Kernel.SporCov.PermKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.LocalAnalysis.StandardType.GGSporKRestM11Abs
public import CFSG.LocalAnalysis.StandardType.GGSporKRestMaxPair
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.KD.SporCovPerm.M11

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.Blueprint CFSG.Sporadic.Mathieu

open scoped Pointwise

abbrev 𝔾 : Type := ↥NativeSporadic.M11

local notation "ev" => wE (fP m11a m11b)

theorem hA : ∀ x < 11, fA x = idx 11 m11a x := by decide +kernel

theorem hAi : ∀ x < 11, fAi x = idx 11 m11a⁻¹ x :=
  inv_of_left hA (by decide +kernel)

theorem hB : ∀ x < 11, fB x = idx 11 m11b x := by decide +kernel

theorem hBi : ∀ x < 11, fBi x = idx 11 m11b⁻¹ x :=
  inv_of_left hB (by decide +kernel)

theorem bs_eq : bs = List.range 11 := by decide +kernel

theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

theorem mem_bs {x : ℕ} (hx : x ∈ bs) : x < 11 := by
  rw [bs_eq] at hx
  exact List.mem_range.1 hx

theorem im_eq (w : List ℕ) {x : ℕ} (hx : x < 11) : im w x = idx 11 (ev w) x :=
  imB_eq hA hAi hB hBi w hx

theorem ev_append (u v : List ℕ) : ev (u ++ v) = ev v * ev u :=
  wE_append _ u v

theorem ext_idx {g h : 𝔾} (H : ∀ x < 11, idx 11 g x = idx 11 h x) : g = h := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have e := H x.val x.isLt
  rw [PermKit.idx_coe g x.isLt, PermKit.idx_coe h x.isLt] at e
  exact Fin.ext e

theorem E_sound {u v : List ℕ} (h : E u v = true) : ev u = ev v := by
  apply ext_idx
  intro x hx
  have e := eqB_spec h x (by rw [bs_eq]; exact List.mem_range.2 hx)
  rw [← im_eq u hx, ← im_eq v hx]
  exact e

theorem E_complete {u v : List ℕ} (h : ev u = ev v) : E u v = true := by
  unfold E
  apply eqB_of
  intro x hx
  change im u x = im v x
  rw [im_eq u (mem_bs hx), im_eq v (mem_bs hx), h]

theorem ev_one {u : List ℕ} (h : E u [] = true) : ev u = 1 :=
  E_sound h

theorem model : Model letP E ev := by
  have h := (PermKit.model (K := NativeSporadic.M11) hA hAi hB hBi).1
  rw [← bs_eq] at h
  exact h

theorem keyL_congr {f g : ℕ → ℕ} : ∀ l : List ℕ, (∀ x ∈ l, f x = g x) → keyL f l = keyL g l
  | [], _ => rfl
  | x :: l, h => by
    change Nat.add (f x) (Nat.mul 16 (keyL f l)) = Nat.add (g x) (Nat.mul 16 (keyL g l))
    rw [h x List.mem_cons_self, keyL_congr l fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem key_congr {u v : List ℕ} (h : ev u = ev v) : key u = key v := by
  unfold key
  apply keyL_congr
  intro x hx
  rw [im_eq u (mem_bs hx), im_eq v (mem_bs hx), h]

theorem lt_of_adj {f : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, f i < f (i + 1)) :
    ∀ i j, i < j → j ≤ n → f i < f j := by
  intro i j hij hjn
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact (ih h' (by omega)).trans (h j (by omega))
    · subst h'
      exact h i (by omega)

theorem nodup_of_adj {w : ℕ → List ℕ} {n : ℕ} (h : ∀ i < n, key (w i) < key (w (i + 1))) :
    ((List.range (n + 1)).map fun i => ev (w i)).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj e
  have hk := key_congr e
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · have := lt_of_adj (f := fun k => key (w k)) h i j hl (by omega)
    omega
  · have := lt_of_adj (f := fun k => key (w k)) h j i hl (by omega)
    omega

theorem parts : chS0 = true ∧ chS = true ∧ chN = true ∧ chNS = true ∧ chNC = true ∧ chP = true ∧
    chG = true := by
  have h := Ck.ok
  unfold chk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem val_smul (g : 𝔾) (x : Fin 11) : (g • x).val = idx 11 g x.val :=
  (idx_of_lt g x.isLt).symm

theorem smul_eq_of_im {u v : List ℕ} {x y : Fin 11} (h : im u x.val = im v y.val) :
    ev u • x = ev v • y := by
  apply Fin.ext
  rw [val_smul, val_smul, ← im_eq u x.isLt, ← im_eq v y.isLt]
  exact h

theorem smul_pair (g : 𝔾) (x y : Fin 11) : g • ({x, y} : Finset (Fin 11)) = {g • x, g • y} := by
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton]

theorem fin_lt_two (z : Fin 11) : (z = 0 ∨ z = 1) ↔ z.val < 2 := by
  fin_cases z <;> simp

theorem pair_eq_iff {u v : Fin 11} (huv : u ≠ v) :
    ({u, v} : Finset (Fin 11)) = {0, 1} ↔ (u = 0 ∨ u = 1) ∧ (v = 0 ∨ v = 1) := by
  constructor
  · intro h
    have hu : u ∈ ({u, v} : Finset (Fin 11)) := by simp
    have hv : v ∈ ({u, v} : Finset (Fin 11)) := by simp
    rw [h] at hu hv
    exact ⟨by simpa using hu, by simpa using hv⟩
  · rintro ⟨hu | hu, hv | hv⟩ <;> subst hu <;> subst hv
    · exact absurd rfl huv
    · rfl
    · exact Finset.pair_comm 1 0
    · exact absurd rfl huv

@[expose] noncomputable def N : Subgroup 𝔾 := MulAction.stabilizer 𝔾 ({0, 1} : Finset (Fin 11))

theorem smul_ne (g : 𝔾) : g • (0 : Fin 11) ≠ g • (1 : Fin 11) := by
  intro h
  exact absurd (smul_left_cancel g h) (by decide)

theorem mem_N_iff (g : 𝔾) : g ∈ N ↔ idx 11 g 0 < 2 ∧ idx 11 g 1 < 2 := by
  unfold N
  rw [MulAction.mem_stabilizer_iff, smul_pair, pair_eq_iff (smul_ne g), fin_lt_two, fin_lt_two,
    val_smul, val_smul]
  rfl

theorem pf_mem {w : List ℕ} (h : pf w = true) : ev w ∈ N := by
  unfold pf at h
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, im_eq w (by norm_num), im_eq w (by norm_num)] at h
  exact (mem_N_iff _).2 h

theorem pair_cover {x y : Fin 11} (hxy : x < y) (h01 : ¬(x = 0 ∧ y = 1)) :
    ∃ n ∈ N, ∃ i < 2, n • ({x, y} : Finset (Fin 11)) = ev (nthW F.H i) • ({0, 1} : Finset (Fin 11)) := by
  have h := parts.2.2.2.2.2.1
  unfold chP at h
  rw [allLt_iff] at h
  have h := h x.val x.isLt
  rw [allLt_iff] at h
  have h := h y.val y.isLt
  have hlt : Nat.blt x.val y.val = true := blt_iff.2 hxy
  have h01' : (Nat.beq x.val 0 && Nat.beq y.val 1) = false := by
    rw [Bool.and_eq_false_iff, ← Bool.not_eq_true, ← Bool.not_eq_true, Nat.beq_eq, Nat.beq_eq]
    by_contra hc
    push Not at hc
    exact h01 ⟨Fin.ext hc.1, Fin.ext hc.2⟩
  rw [hlt, h01', Bool.not_true, Bool.false_or, Bool.false_or] at h
  unfold pairOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨hpf, hi⟩, hc⟩ := h
  refine ⟨_, pf_mem hpf, _, hi, ?_⟩
  rw [smul_pair, smul_pair]
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [smul_eq_of_im (y := 0) h1, smul_eq_of_im (y := 1) h2]
  · rw [smul_eq_of_im (y := 1) h1, smul_eq_of_im (y := 0) h2, Finset.pair_comm]

theorem orbit_eq :
    MulAction.orbit 𝔾 ({0, 1} : Finset (Fin 11)) =
      (↑(Finset.powersetCard 2 (Finset.univ : Finset (Fin 11))) : Set (Finset (Fin 11))) := by
  ext s
  rw [MulAction.mem_orbit_iff,
    show s ∈ (↑(Finset.powersetCard 2 (Finset.univ : Finset (Fin 11))) : Set (Finset (Fin 11))) ↔
        s.card = 2 from by simp [Finset.mem_powersetCard]]
  have key : ∀ x y : Fin 11, x < y → ∃ g : 𝔾, g • ({0, 1} : Finset (Fin 11)) = {x, y} := by
    intro x y hxy
    by_cases h01 : x = 0 ∧ y = 1
    · obtain ⟨rfl, rfl⟩ := h01
      exact ⟨1, one_smul _ _⟩
    · obtain ⟨n, -, i, -, hn⟩ := pair_cover hxy h01
      refine ⟨n⁻¹ * ev (nthW F.H i), ?_⟩
      rw [mul_smul, ← hn, inv_smul_smul]
  constructor
  · rintro ⟨g, rfl⟩
    rw [Finset.card_smul_finset]
    decide
  · intro hs2
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs2
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact key x y hlt
    · obtain ⟨g, hg⟩ := key y x hgt
      exact ⟨g, by rw [hg, Finset.pair_comm]⟩

theorem card_N : Nat.card N = 144 := by
  haveI : Fintype 𝔾 := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.orbit 𝔾 ({0, 1} : Finset (Fin 11))) := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer 𝔾 ({0, 1} : Finset (Fin 11))) := Fintype.ofFinite _
  have horbit : Fintype.card ↥(MulAction.orbit 𝔾 ({0, 1} : Finset (Fin 11))) = 55 := by
    rw [← Nat.card_eq_fintype_card, orbit_eq, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    decide
  have hK : Fintype.card 𝔾 = 7920 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_M11
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group 𝔾 ({0, 1} : Finset (Fin 11))
  rw [horbit, hK] at hOS
  unfold N
  rw [Nat.card_eq_fintype_card]
  omega

theorem length_le_card {H : Subgroup 𝔾} {L : List 𝔾} (hnd : L.Nodup) (hL : ∀ g ∈ L, g ∈ H) :
    L.length ≤ Nat.card H := by
  classical
  have hinj : Function.Injective
      (fun x : {x // x ∈ L.toFinset} => (⟨x.1, hL x.1 (List.mem_toFinset.1 x.2)⟩ : H)) := by
    intro x y e
    exact Subtype.ext (by simpa using congrArg Subtype.val e)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd] at this

theorem chN_facts : (∀ t < 143, key (nW t) < key (nW (t + 1))) ∧ ∀ t < 144, pf (nW t) = true := by
  have h := parts.2.2.1
  unfold chN at h
  rw [Bool.and_eq_true, allLt_iff, allLt_iff] at h
  exact ⟨fun t ht => blt_iff.1 (h.1 t ht), h.2⟩

theorem mem_table {g : 𝔾} (hg : g ∈ N) : ∃ t < 144, g = ev (nW t) := by
  by_contra hc
  push Not at hc
  have hnd := nodup_of_adj chN_facts.1
  have hmem : ∀ x ∈ g :: (List.range (143 + 1)).map fun i => ev (nW i), x ∈ N := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hg
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      exact pf_mem (chN_facts.2 t (List.mem_range.1 ht))
  have hnd' : (g :: (List.range (143 + 1)).map fun i => ev (nW i)).Nodup := by
    refine List.nodup_cons.2 ⟨?_, hnd⟩
    intro hx
    obtain ⟨t, ht, e⟩ := List.mem_map.1 hx
    exact hc t (List.mem_range.1 ht) e.symm
  have := length_le_card hnd' hmem
  rw [card_N, List.length_cons, List.length_map, List.length_range] at this
  omega

theorem sW_cases (k : ℕ) : sW k = F.S1 ∨ sW k = F.S2 := by
  unfold sW
  cases Nat.beq k 0 <;> simp

@[expose] noncomputable def S : Subgroup 𝔾 := Subgroup.closure {g | g ∈ [ev F.S1, ev F.S2]}

theorem sW_mem (k : ℕ) : ev (sW k) ∈ S := by
  rcases sW_cases k with e | e <;> rw [e] <;> exact Subgroup.subset_closure (by simp)

theorem sT_mem (i : ℕ) : ev (sT i) ∈ S := by
  unfold sT
  apply model.mem_expC
  intro k
  rcases nthW_mem_or [F.S1, F.S2] k with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> rw [h] <;> exact Subgroup.subset_closure (by simp)
  · rw [h]
    exact S.one_mem

@[expose] noncomputable def TS : List 𝔾 := (List.range (8 + 1)).map fun i => ev (sT i)

theorem chS_facts : F.J1 < 9 ∧ E (sT F.J1) [] = true ∧
    (∀ i < 8, key (sT i) < key (sT (i + 1))) ∧
    ∀ i < 9, ∀ k < 2, nthN F.SM (4 * i + 2 * k) < 9 ∧
      E (sW k ++ sT i) (sT (nthN F.SM (4 * i + 2 * k))) = true ∧
      nthN F.SM (4 * i + 2 * k + 1) < 9 ∧
      E (sT i) (sW k ++ sT (nthN F.SM (4 * i + 2 * k + 1))) = true := by
  have h := parts.2.1
  unfold chS at h
  simp only [Bool.and_eq_true, allLt_iff, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi k hk => ?_⟩
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h4 i hi k hk
  exact ⟨a1, a2, a3, a4⟩

theorem mem_TS {x : 𝔾} : x ∈ TS ↔ ∃ i < 9, ev (sT i) = x := by
  unfold TS
  simp

theorem card_S : Nat.card S = 9 := by
  obtain ⟨hJ, hJ1, hinc, hcl⟩ := chS_facts
  have h1 : (1 : 𝔾) ∈ TS := mem_TS.2 ⟨_, hJ, ev_one hJ1⟩
  have hgen : ∀ t ∈ TS, t ∈ Subgroup.closure {g | g ∈ [ev F.S1, ev F.S2]} := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := mem_TS.1 ht
    exact sT_mem i
  have hmul : ∀ t ∈ TS, ∀ g ∈ [ev F.S1, ev F.S2], t * g ∈ TS ∧ t * g⁻¹ ∈ TS := by
    intro t ht g hg
    obtain ⟨i, hi, rfl⟩ := mem_TS.1 ht
    have hk : ∃ k < 2, g = ev (sW k) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hk
    obtain ⟨a1, a2, a3, a4⟩ := hcl i hi k hk
    refine ⟨mem_TS.2 ⟨_, a1, ?_⟩, mem_TS.2 ⟨_, a3, ?_⟩⟩
    · rw [← E_sound a2, ev_append]
    · rw [E_sound a4, ev_append, mul_inv_cancel_right]
  have hcard := sporKRest_card_closure_of_table _ TS h1 hmul hgen (nodup_of_adj hinc)
  unfold S
  rw [hcard]
  unfold TS
  simp

theorem mem_S_iff (x : 𝔾) : x ∈ S ↔ ∃ i < 9, ev (sT i) = x := by
  obtain ⟨hJ, hJ1, hinc, hcl⟩ := chS_facts
  have h1 : (1 : 𝔾) ∈ TS := mem_TS.2 ⟨_, hJ, ev_one hJ1⟩
  rw [← mem_TS]
  constructor
  · intro hx
    by_contra hn
    have hnd : (x :: TS).Nodup := List.nodup_cons.2 ⟨hn, nodup_of_adj hinc⟩
    have hle := length_le_card hnd (by
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact hx
      · obtain ⟨i, -, rfl⟩ := mem_TS.1 hg
        exact sT_mem i)
    rw [card_S, List.length_cons] at hle
    unfold TS at hle
    simp at hle
  · intro hx
    obtain ⟨i, -, rfl⟩ := mem_TS.1 hx
    exact sT_mem i

theorem chS0_facts : im F.S1 0 = 0 ∧ im F.S1 1 = 1 ∧ im F.S2 0 = 0 ∧ im F.S2 1 = 1 ∧
    ∀ x < 11, 2 ≤ x → im F.S1 x ≠ x ∨ im F.S2 x ≠ x := by
  have h := parts.1
  unfold chS0 at h
  simp only [Bool.and_eq_true, allLt_iff, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx h2x => ?_⟩
  have h := h5 x hx
  simp only [Bool.or_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · omega
  · exact Or.inl fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide)
  · exact Or.inr fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide)

theorem S_fix (z : Fin 11) (hz : z.val < 2) : ∀ s ∈ S, s • z = z := by
  obtain ⟨h1, h2, h3, h4, -⟩ := chS0_facts
  have hle : S ≤ MulAction.stabilizer 𝔾 z := by
    unfold S
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    apply Fin.ext
    rw [val_smul]
    rcases (fin_lt_two z).2 hz with rfl | rfl <;> rcases hg with rfl | rfl
    · rw [← im_eq _ (by norm_num)]
      exact h1
    · rw [← im_eq _ (by norm_num)]
      exact h3
    · rw [← im_eq _ (by norm_num)]
      exact h2
    · rw [← im_eq _ (by norm_num)]
      exact h4
  intro s hs
  exact hle hs

theorem S_moved (y : Fin 11) (hy : 2 ≤ y.val) : ∃ s ∈ S, s • y ≠ y := by
  obtain ⟨-, -, -, -, h5⟩ := chS0_facts
  rcases h5 y.val y.isLt hy with h | h
  · refine ⟨ev F.S1, Subgroup.subset_closure (by simp), fun e => h ?_⟩
    have := congrArg Fin.val e
    rwa [val_smul, ← im_eq _ y.isLt] at this
  · refine ⟨ev F.S2, Subgroup.subset_closure (by simp), fun e => h ?_⟩
    have := congrArg Fin.val e
    rwa [val_smul, ← im_eq _ y.isLt] at this

theorem norm_le_N {g : 𝔾} (hg : g ∈ Subgroup.normalizer (S : Set 𝔾)) : g ∈ N := by
  have key : ∀ z : Fin 11, z.val < 2 → (g • z).val < 2 := by
    intro z hz
    by_contra hc
    push Not at hc
    obtain ⟨s, hs, hne⟩ := S_moved (g • z) hc
    have hc' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.1 hg s).1 hs
    have hfix := S_fix z hz _ hc'
    apply hne
    rw [mul_smul, mul_smul] at hfix
    calc s • g • z = g • g⁻¹ • s • g • z := (smul_inv_smul g _).symm
      _ = g • z := by rw [hfix]
  rw [mem_N_iff]
  have h0 := key 0 (by decide)
  have h1 := key 1 (by decide)
  rw [val_smul] at h0 h1
  exact ⟨h0, h1⟩

theorem chNS_facts : ∀ t < 144, ∀ k < 2, nthN F.NS (2 * t + k) < 9 ∧
    E (sW k ++ nW t) (nW t ++ sT (nthN F.NS (2 * t + k))) = true := by
  have h := parts.2.2.2.1
  unfold chNS at h
  simp only [Bool.and_eq_true, allLt_iff, Nat.blt_eq] at h
  exact h

theorem conj_mem {g : 𝔾} (hg : g ∈ N) :
    ∀ y ∈ S, g * y * g⁻¹ ∈ S := by
  obtain ⟨t, ht, rfl⟩ := mem_table hg
  have hgen : ∀ k < 2, ev (nW t) * ev (sW k) * (ev (nW t))⁻¹ ∈ S := by
    intro k hk
    obtain ⟨-, h2⟩ := chNS_facts t ht k hk
    have e := E_sound h2
    rw [ev_append, ev_append] at e
    rw [e, mul_inv_cancel_right]
    exact sT_mem _
  intro y hy
  unfold S at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hgen 0 (by norm_num)
    · exact hgen 1 (by norm_num)
  | one => rw [mul_one, mul_inv_cancel]; exact S.one_mem
  | mul x z _ _ hx hz =>
    have e : ev (nW t) * (x * z) * (ev (nW t))⁻¹ =
        (ev (nW t) * x * (ev (nW t))⁻¹) * (ev (nW t) * z * (ev (nW t))⁻¹) := by group
    rw [e]
    exact S.mul_mem hx hz
  | inv x _ hx =>
    have e : ev (nW t) * x⁻¹ * (ev (nW t))⁻¹ = (ev (nW t) * x * (ev (nW t))⁻¹)⁻¹ := by group
    rw [e]
    exact S.inv_mem hx

theorem norm_eq : Subgroup.normalizer (S : Set 𝔾) = N := by
  ext g
  refine ⟨norm_le_N, fun hg => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem hg h, fun hh => ?_⟩
  have := conj_mem (N.inv_mem hg) _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem cent :
    ∀ t ∈ N, (∀ s ∈ S, t * s = s * t) → t ∈ S := by
  intro g hg hc
  obtain ⟨t, ht, rfl⟩ := mem_table hg
  have h := parts.2.2.2.2.1
  unfold chNC at h
  rw [allLt_iff] at h
  have h := h t ht
  cases hb : Nat.blt (nthN F.NC t) 9
  · rw [hb, cond_false, Bool.not_eq_true'] at h
    have e : ev (sW (nthN F.NC t - 9) ++ nW t) = ev (nW t ++ sW (nthN F.NC t - 9)) := by
      rw [ev_append, ev_append]
      exact hc _ (sW_mem _)
    rw [E_complete e] at h
    exact absurd h (by decide)
  · rw [hb, cond_true] at h
    rw [mem_S_iff]
    exact ⟨_, blt_iff.1 hb, (E_sound h).symm⟩

theorem chG_facts : pf F.N1 = true ∧ pf F.N2 = true ∧ E (F.N1 ++ F.N1i) [] = true ∧
    E (F.N2 ++ F.N2i) [] = true ∧ ∀ i < 2, E (nthW F.H i ++ nthW F.HI i) [] = true ∧
      E (expC (gM i) (nthW F.WA i)) [0] = true ∧ E (expC (gM i) (nthW F.WB i)) [2] = true := by
  have h := parts.2.2.2.2.2.2
  unfold chG at h
  simp only [Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun i hi => ⟨(h5 i hi).1.1, (h5 i hi).1.2, (h5 i hi).2⟩⟩

theorem inv_eq {u v : List ℕ} (h : E (u ++ v) [] = true) : ev v = (ev u)⁻¹ := by
  have e := ev_one h
  rw [ev_append] at e
  exact eq_inv_of_mul_eq_one_left e

theorem gen_top (i : ℕ) (hi : i < 2) :
    Subgroup.closure ((N : Set 𝔾) ∪ {ev (nthW F.H i)}) = ⊤ := by
  obtain ⟨p1, p2, e1, e2, hw⟩ := chG_facts
  obtain ⟨eh, ea, eb⟩ := hw i hi
  set T := Subgroup.closure ((N : Set 𝔾) ∪ {ev (nthW F.H i)})
  have hN : ∀ g ∈ N, g ∈ T := fun g hg => Subgroup.subset_closure (Set.mem_union_left _ hg)
  have hh : ev (nthW F.H i) ∈ T := Subgroup.subset_closure (Set.mem_union_right _ rfl)
  have hlet : ∀ k, ev (nthW (gM i) k) ∈ T := by
    intro k
    rcases k with _ | _ | _ | _ | _ | _ | k
    · exact hN _ (pf_mem p1)
    · change ev F.N1i ∈ T
      rw [inv_eq e1]
      exact T.inv_mem (hN _ (pf_mem p1))
    · exact hN _ (pf_mem p2)
    · change ev F.N2i ∈ T
      rw [inv_eq e2]
      exact T.inv_mem (hN _ (pf_mem p2))
    · exact hh
    · change ev (nthW F.HI i) ∈ T
      rw [inv_eq eh]
      exact T.inv_mem hh
    · rw [nthW_ge _ _ (by simp [gM])]
      exact T.one_mem
  have ha := model.mem_expC hlet (nthW F.WA i)
  have hb := model.mem_expC hlet (nthW F.WB i)
  rw [E_sound ea] at ha
  rw [E_sound eb] at hb
  apply PermKit.top_of_seeds m11_eq (R := [[0], [2]]) rfl rfl
  intro k
  rcases k with _ | _ | k
  · exact ha
  · exact hb
  · rw [nthW_ge _ _ (by simp)]
    exact T.one_mem

theorem N_max : ∀ Y : Subgroup 𝔾, N ≤ Y → Y = N ∨ Y = ⊤ := by
  let hsL : List 𝔾 := [ev (nthW F.H 0), ev (nthW F.H 1)]
  have hcover : ∀ g : 𝔾, g • ({0, 1} : Finset (Fin 11)) ≠ {0, 1} →
      ∃ n ∈ MulAction.stabilizer 𝔾 ({0, 1} : Finset (Fin 11)), ∃ h ∈ hsL,
        n • g • ({0, 1} : Finset (Fin 11)) = h • ({0, 1} : Finset (Fin 11)) := by
    intro g hg
    rw [smul_pair] at hg ⊢
    set u := g • (0 : Fin 11)
    set v := g • (1 : Fin 11)
    have huv : u ≠ v := smul_ne g
    have key : ∀ x y : Fin 11, x < y → ({u, v} : Finset (Fin 11)) = {x, y} →
        ∃ n ∈ MulAction.stabilizer 𝔾 ({0, 1} : Finset (Fin 11)), ∃ h ∈ hsL,
          n • ({u, v} : Finset (Fin 11)) = h • ({0, 1} : Finset (Fin 11)) := by
      intro x y hxy e
      have h01 : ¬(x = 0 ∧ y = 1) := by
        rintro ⟨rfl, rfl⟩
        exact hg e
      obtain ⟨n, hn, i, hi, hni⟩ := pair_cover hxy h01
      refine ⟨n, hn, ev (nthW F.H i), ?_, by rw [e, hni]⟩
      rcases i with _ | _ | i
      · simp [hsL]
      · simp [hsL]
      · omega
    rcases lt_or_gt_of_ne huv with hl | hl
    · exact key u v hl rfl
    · exact key v u hl (Finset.pair_comm u v)
  have hgen : ∀ h ∈ hsL,
      Subgroup.closure ((MulAction.stabilizer 𝔾 ({0, 1} : Finset (Fin 11)) : Set 𝔾) ∪ {h}) = ⊤ := by
    intro h hh
    simp only [hsL, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact gen_top 0 (by norm_num)
    · exact gen_top 1 (by norm_num)
  exact sporKRest_stabilizer_maximal ({0, 1} : Finset (Fin 11)) hsL hcover hgen

theorem m11_exists_sylow :
    ∃ S₀ : Sylow 3 ↥NativeSporadic.M11,
      (∀ Y : Subgroup ↥NativeSporadic.M11,
        Subgroup.normalizer ((S₀ : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ≤ Y →
          Y = Subgroup.normalizer ((S₀ : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ∨
            Y = ⊤) ∧
      IsPGroup 3 ↥(CFSG.generalizedFitting
        ↥(Subgroup.normalizer ((S₀ : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11))) :=
  sporKRest_exists_sylow_of_normalizer S N card_M11 card_S card_N norm_eq cent N_max

end CFSG.KD.SporCovPerm.M11

end
