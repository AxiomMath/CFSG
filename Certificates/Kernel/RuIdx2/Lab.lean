module

public import Certificates.Kernel.RuIdx2.Sem
public import Certificates.Kernel.RuIdx2.DefsV
import Certificates.Kernel.RuIdx2.V
import Certificates.Kernel.RuIdx2.W

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2.Lab

open CFSG.KD.RuIdx2 CFSG.KD.RuIdx2.Sem CFSG.KC.RuIdx2 CFSG.KC.Enum CFSG.KD.Ru4120 CFSG.KS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.K1262Two.RuP

theorem wltK_spec {W : Nat} (h : wltK W = true) : ∀ c ∈ unW W, c < 10 := by
  intro c hc
  rw [unW_eq] at hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  unfold wltK at h
  rw [PK.allBlk_eq, List.all_eq_true] at h
  have h1 := h i hi
  rw [Nat.zero_add, Nat.blt_eq] at h1
  exact h1

theorem RW_lt {u : Nat} (hu : u < 7) {i : Nat} (hi : i < nR u) : ∀ c ∈ unW (RW u i), c < 10 := by
  have h := V.all u hu
  unfold famV at h
  exact wltK_spec (PK.allN_iff.1 h i hi)

section Group

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 4060)] {a b : Γ}

theorem letK_mul (h : H.Ctx a b) {f : Nat → Nat} {c : Nat} (hk : letK LC f 4060 c = true) :
    lt a b (f c) * lt a b c = 1 := by
  refine h.base _ fun p hp => ?_
  have hp' : p < 4060 := H.hB p hp
  unfold letK at hk
  simp only [PK.strictB_eq] at hk
  have h1 := PK.allN_iff.1 hk p hp'
  rw [act_mul _ _ hp', act_let h _ (act_lt _ hp'), act_let h _ hp']
  exact Nat.eq_of_beq_eq_true h1

theorem lt_IL (h : H.Ctx a b) {c : Nat} (hc : c < 10) : lt a b (IL c) = (lt a b c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (letK_mul h (I.all c hc))

theorem lt_sq (h : H.Ctx a b) {c : Nat} (hc2 : 2 ≤ c) (hc5 : c < 5) : lt a b c * lt a b c = 1 := by
  have hq : ∀ j < 4, letK LC IdL 4060 (List.getD [0, 2, 3, 4] j 0) = true := Q.all
  interval_cases c
  · exact letK_mul (f := IdL) h (hq 1 (by norm_num))
  · exact letK_mul (f := IdL) h (hq 2 (by norm_num))
  · exact letK_mul (f := IdL) h (hq 3 (by norm_num))

theorem E_gs {c : Nat} (hc : c < 3) : G.E a b (gs.getD c 0) = lt a b (c + 2) := by
  interval_cases c <;> rfl

theorem RX_eq : H.RX a b = Subgroup.closure {x | x ∈ [lt a b 2, lt a b 3, lt a b 4]} := rfl

theorem lt_mem {c : Nat} (hc2 : 2 ≤ c) (hc5 : c < 5) : lt a b c ∈ H.RX a b := by
  rw [RX_eq]
  refine Subgroup.subset_closure ?_
  interval_cases c <;> simp

theorem X_mem_inj [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) :
    (∀ k < 16384, H.X a b k ∈ H.RX a b) ∧
      ∀ k < 16384, ∀ k' < 16384, H.X a b k = H.X a b k' → k = k' := by
  classical
  let F : Fin 16384 → Γ := fun k => H.X a b k
  have hsub : (H.RX a b : Set Γ) ⊆ ↑(Finset.univ.image F) := by
    intro g hg
    obtain ⟨k, hk, e⟩ := H.mem_X h hg
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨k, hk⟩, Finset.mem_univ _, e⟩)
  have hR : (H.RX a b : Set Γ).ncard = 16384 := by
    rw [← Nat.card_coe_set_eq]
    exact hc
  have hle : 16384 ≤ (Finset.univ.image F).card := by
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, hR] at h1
    exact h1
  have hcard : (Finset.univ.image F).card = 16384 :=
    le_antisymm (Finset.card_image_le.trans (by simp)) hle
  have hinj : Function.Injective F := by
    rw [← Set.injOn_univ, ← Finset.coe_univ, ← Finset.card_image_iff, hcard]
    simp
  have heq : (H.RX a b : Set Γ) = ↑(Finset.univ.image F) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset, hcard, hR])
      (Finset.finite_toSet _)
  refine ⟨fun k hk => ?_, fun k hk k' hk' e => ?_⟩
  · have hm : H.X a b k ∈ (↑(Finset.univ.image F) : Set Γ) :=
      Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩)
    rw [← heq] at hm
    exact hm
  · have e' : F ⟨k, hk⟩ = F ⟨k', hk'⟩ := by
      simp only [F]
      exact e
    exact congrArg Fin.val (hinj e')

theorem X_mem [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) {k : Nat}
    (hk : k < 16384) : H.X a b k ∈ H.RX a b :=
  (X_mem_inj h hc).1 k hk

theorem X_inj [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) {k k' : Nat}
    (hk : k < 16384) (hk' : k' < 16384) (e : H.X a b k = H.X a b k') : k = k' :=
  (X_mem_inj h hc).2 k hk k' hk' e

open Classical in
@[expose] noncomputable def kOf (a b g : Γ) : Nat :=
  if hg : ∃ k < 16384, H.X a b k = g then hg.choose else 0

theorem kOf_spec [Finite Γ] (h : H.Ctx a b) {g : Γ} (hg : g ∈ H.RX a b) :
    kOf a b g < 16384 ∧ H.X a b (kOf a b g) = g := by
  have hex : ∃ k < 16384, H.X a b k = g := H.mem_X h hg
  unfold kOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem kOf_X [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) {k : Nat}
    (hk : k < 16384) : kOf a b (H.X a b k) = k := by
  obtain ⟨h1, h2⟩ := kOf_spec h (X_mem h hc hk)
  exact X_inj h hc h1 hk h2

@[expose] noncomputable def lab (a b : Γ) (vm : Nat) (g : Γ) : ZMod 2 :=
  ((par vm (psi (kOf a b g)) : Nat) : ZMod 2)

theorem lab_X [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) (vm : Nat)
    {k : Nat} (hk : k < 16384) : lab a b vm (H.X a b k) = ((par vm (psi k) : Nat) : ZMod 2) := by
  unfold lab
  rw [kOf_X h hc hk]

theorem par_zero : ∀ vm < 8, par vm 0 = 0 := by decide

theorem lab_one [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) {vm : Nat}
    (hvm : vm < 8) : lab a b vm 1 = 0 := by
  rw [← H.X_one h, lab_X h hc vm (by norm_num), Nat.eq_of_beq_eq_true one, par_zero vm hvm]
  rfl

theorem lab_step [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) {vm : Nat}
    (hvm : vm < 8) {c : Nat} (hc3 : c < 3) {g : Γ} (hg : g ∈ H.RX a b) :
    lab a b vm (lt a b (c + 2) * g) = lab a b vm g + ((par vm (2 ^ c) : Nat) : ZMod 2) := by
  obtain ⟨hk, hX⟩ := kOf_spec h hg
  obtain ⟨ht, hXt⟩ := H.X_tg h hk hc3
  rw [E_gs hc3, hX] at hXt
  rw [← hXt, lab_X h hc vm ht]
  unfold lab
  have hps : psi (tg c (kOf a b g)) = Nat.xor (psi (kOf a b g)) (2 ^ c) := by
    obtain ⟨h0, h1, h2⟩ := labK_spec hk
    interval_cases c
    exacts [h0, h1, h2]
  rw [hps]
  exact par_xor vm hvm _ (psi_lt _) c hc3

theorem lab_lt [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) {vm : Nat}
    (hvm : vm < 8) {c : Nat} (hc2 : 2 ≤ c) (hc5 : c < 5) :
    lab a b vm (lt a b c) = ((par vm (2 ^ (c - 2)) : Nat) : ZMod 2) := by
  have e := lab_step h hc hvm (c := c - 2) (by omega) (H.RX a b).one_mem
  rw [mul_one, lab_one h hc hvm, zero_add, Nat.sub_add_cancel hc2] at e
  exact e

theorem lab_prod [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) {vm : Nat}
    (hvm : vm < 8) (L : List Nat) (hL : ∀ c ∈ L, 2 ≤ c ∧ c < 5) :
    lab a b vm ((L.map (lt a b)).prod) =
      (L.map fun c => ((par vm (2 ^ (c - 2)) : Nat) : ZMod 2)).sum := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil, lab_one h hc hvm, List.map_nil, List.sum_nil]
  | cons c L ih =>
    have hc' := hL c (List.mem_cons.2 (Or.inl rfl))
    have hL' : ∀ d ∈ L, 2 ≤ d ∧ d < 5 := fun d hd => hL d (List.mem_cons.2 (Or.inr hd))
    have hmem : (L.map (lt a b)).prod ∈ H.RX a b := by
      refine (H.RX a b).list_prod_mem fun x hx => ?_
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      exact lt_mem (hL' d hd).1 (hL' d hd).2
    have e := lab_step h hc hvm (c := c - 2) (by omega) hmem
    rw [Nat.sub_add_cancel hc'.1] at e
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, e, ih hL', add_comm]

@[expose] noncomputable def RS (a b : Γ) (u : Nat) : List Γ :=
  (List.range (nr u)).map fun l => wE a b (RG u l)

@[expose] noncomputable def Rv (a b : Γ) (u : Nat) : Subgroup Γ :=
  Subgroup.closure {x | x ∈ RS a b u}

theorem gen_mem {u l : Nat} (hl : l < nr u) : wE a b (RG u l) ∈ Rv a b u :=
  Subgroup.subset_closure (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)

theorem wE_of {W : Nat} {L : List Nat} (e : unW W = L) : wE a b W = (L.map (lt a b)).prod := by
  unfold wE
  rw [e]

theorem RG_let : ∀ u < 7, ∀ l < nr u, ∀ c ∈ unW (RG u l), 2 ≤ c ∧ c < 5 := by decide +kernel

theorem RG_par : ∀ u < 7, ∀ l < nr u,
    ((unW (RG u l)).map fun c => ((par (vm u) (2 ^ (c - 2)) : Nat) : ZMod 2)).sum = 0 := by
  decide +kernel

theorem tau_let : ∀ u < 7, 2 ≤ tau u ∧ tau u < 5 ∧ vm u < 8 ∧
    ((par (vm u) (2 ^ (tau u - 2)) : Nat) : ZMod 2) = 1 := by decide +kernel

theorem caseA {R : Subgroup Γ} {s τ : Γ} (h1 : s ∈ R) (h2 : τ * s * τ ∈ R) :
    (s ∈ R ∧ τ * s * τ ∈ R) ∨ (τ * s ∈ R ∧ s * τ ∈ R) := Or.inl ⟨h1, h2⟩

theorem caseB {R : Subgroup Γ} {s τ : Γ} (hs : s * s = 1) (hτ : τ * τ = 1) (h : s * τ ∈ R) :
    (s ∈ R ∧ τ * s * τ ∈ R) ∨ (τ * s ∈ R ∧ s * τ ∈ R) := by
  refine Or.inr ⟨?_, h⟩
  have e : τ * s = (s * τ)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hτ, inv_eq_of_mul_eq_one_right hs]
  rw [e]
  exact R.inv_mem h

theorem caseT {R : Subgroup Γ} {τ : Γ} (hτ : τ * τ = 1) :
    (τ ∈ R ∧ τ * τ * τ ∈ R) ∨ (τ * τ ∈ R ∧ τ * τ ∈ R) := by
  rw [hτ]
  exact Or.inr ⟨R.one_mem, R.one_mem⟩

theorem gen_eq {u l : Nat} {L : List Nat} (hl : l < nr u) (e : unW (RG u l) = L) :
    (L.map (lt a b)).prod ∈ Rv a b u := by
  rw [← wE_of e]
  exact gen_mem hl

theorem hc_v (h : H.Ctx a b) {u : Nat} (hu : u < 7) :
    ∀ s ∈ [lt a b 2, lt a b 3, lt a b 4],
      (s ∈ Rv a b u ∧ lt a b (tau u) * s * lt a b (tau u) ∈ Rv a b u) ∨
        (lt a b (tau u) * s ∈ Rv a b u ∧ s * lt a b (tau u) ∈ Rv a b u) := by
  have q2 := lt_sq h (c := 2) (by norm_num) (by norm_num)
  have q3 := lt_sq h (c := 3) (by norm_num) (by norm_num)
  have q4 := lt_sq h (c := 4) (by norm_num) (by norm_num)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  interval_cases u
  ·
    have g0 := gen_eq (a := a) (b := b) (u := 0) (l := 0) (by decide)
      (by decide +kernel : unW (RG 0 0) = [3])
    have g1 := gen_eq (a := a) (b := b) (u := 0) (l := 1) (by decide)
      (by decide +kernel : unW (RG 0 1) = [2, 3, 2])
    have g2 := gen_eq (a := a) (b := b) (u := 0) (l := 2) (by decide)
      (by decide +kernel : unW (RG 0 2) = [4])
    have g3 := gen_eq (a := a) (b := b) (u := 0) (l := 3) (by decide)
      (by decide +kernel : unW (RG 0 3) = [2, 4, 2])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at g0 g1 g2 g3
    have et : tau 0 = 2 := rfl
    rw [et]
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact caseT q2
    · exact caseA g0 (by rw [mul_assoc]; exact g1)
    · exact caseA g2 (by rw [mul_assoc]; exact g3)
  ·
    have g0 := gen_eq (a := a) (b := b) (u := 1) (l := 0) (by decide)
      (by decide +kernel : unW (RG 1 0) = [2])
    have g1 := gen_eq (a := a) (b := b) (u := 1) (l := 1) (by decide)
      (by decide +kernel : unW (RG 1 1) = [3, 2, 3])
    have g2 := gen_eq (a := a) (b := b) (u := 1) (l := 2) (by decide)
      (by decide +kernel : unW (RG 1 2) = [4])
    have g3 := gen_eq (a := a) (b := b) (u := 1) (l := 3) (by decide)
      (by decide +kernel : unW (RG 1 3) = [3, 4, 3])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at g0 g1 g2 g3
    have et : tau 1 = 3 := rfl
    rw [et]
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact caseA g0 (by rw [mul_assoc]; exact g1)
    · exact caseT q3
    · exact caseA g2 (by rw [mul_assoc]; exact g3)
  ·
    have g0 := gen_eq (a := a) (b := b) (u := 2) (l := 0) (by decide)
      (by decide +kernel : unW (RG 2 0) = [2])
    have g1 := gen_eq (a := a) (b := b) (u := 2) (l := 1) (by decide)
      (by decide +kernel : unW (RG 2 1) = [4, 2, 4])
    have g2 := gen_eq (a := a) (b := b) (u := 2) (l := 2) (by decide)
      (by decide +kernel : unW (RG 2 2) = [3])
    have g3 := gen_eq (a := a) (b := b) (u := 2) (l := 3) (by decide)
      (by decide +kernel : unW (RG 2 3) = [4, 3, 4])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at g0 g1 g2 g3
    have et : tau 2 = 4 := rfl
    rw [et]
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact caseA g0 (by rw [mul_assoc]; exact g1)
    · exact caseA g2 (by rw [mul_assoc]; exact g3)
    · exact caseT q4
  ·
    have g0 := gen_eq (a := a) (b := b) (u := 3) (l := 0) (by decide)
      (by decide +kernel : unW (RG 3 0) = [3, 2])
    have g1 := gen_eq (a := a) (b := b) (u := 3) (l := 1) (by decide)
      (by decide +kernel : unW (RG 3 1) = [4])
    have g2 := gen_eq (a := a) (b := b) (u := 3) (l := 2) (by decide)
      (by decide +kernel : unW (RG 3 2) = [2, 4, 2])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at g0 g1 g2
    have et : tau 3 = 2 := rfl
    rw [et]
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact caseT q2
    · exact caseB q3 q2 g0
    · exact caseA g1 (by rw [mul_assoc]; exact g2)
  ·
    have g0 := gen_eq (a := a) (b := b) (u := 4) (l := 0) (by decide)
      (by decide +kernel : unW (RG 4 0) = [3])
    have g1 := gen_eq (a := a) (b := b) (u := 4) (l := 1) (by decide)
      (by decide +kernel : unW (RG 4 1) = [2, 3, 2])
    have g2 := gen_eq (a := a) (b := b) (u := 4) (l := 2) (by decide)
      (by decide +kernel : unW (RG 4 2) = [4, 2])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at g0 g1 g2
    have et : tau 4 = 2 := rfl
    rw [et]
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact caseT q2
    · exact caseA g0 (by rw [mul_assoc]; exact g1)
    · exact caseB q4 q2 g2
  ·
    have g0 := gen_eq (a := a) (b := b) (u := 5) (l := 0) (by decide)
      (by decide +kernel : unW (RG 5 0) = [2])
    have g1 := gen_eq (a := a) (b := b) (u := 5) (l := 1) (by decide)
      (by decide +kernel : unW (RG 5 1) = [3, 2, 3])
    have g2 := gen_eq (a := a) (b := b) (u := 5) (l := 2) (by decide)
      (by decide +kernel : unW (RG 5 2) = [4, 3])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at g0 g1 g2
    have et : tau 5 = 3 := rfl
    rw [et]
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact caseA g0 (by rw [mul_assoc]; exact g1)
    · exact caseT q3
    · exact caseB q4 q3 g2
  ·
    have g0 := gen_eq (a := a) (b := b) (u := 6) (l := 0) (by decide)
      (by decide +kernel : unW (RG 6 0) = [3, 2])
    have g1 := gen_eq (a := a) (b := b) (u := 6) (l := 1) (by decide)
      (by decide +kernel : unW (RG 6 1) = [4, 2])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at g0 g1
    have et : tau 6 = 2 := rfl
    rw [et]
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact caseT q2
    · exact caseB q3 q2 g0
    · exact caseB q4 q2 g1

theorem idx2_v [Finite Γ] (h : H.Ctx a b) (hc : Nat.card (H.RX a b) = 2 ^ 14) {u : Nat}
    (hu : u < 7) :
    Rv a b u ≤ H.RX a b ∧ (∀ g ∈ H.RX a b, g ∈ Rv a b u ↔ lab a b (vm u) g = 0) ∧
      Nat.card (H.RX a b) = 2 * Nat.card (Rv a b u) ∧ Nat.card (Rv a b u) = 2 ^ 13 ∧
      lt a b (tau u) ∈ H.RX a b ∧ lt a b (tau u) ∉ Rv a b u ∧
      lt a b (tau u) * lt a b (tau u) = 1 := by
  obtain ⟨ht2, ht5, hvm, hτ1⟩ := tau_let u hu
  have hT : H.RX a b = Subgroup.closure {x | x ∈ [lt a b 2, lt a b 3, lt a b 4]} := RX_eq
  have hS : ∀ s ∈ [lt a b 2, lt a b 3, lt a b 4], s * s = 1 ∧ ∃ v : ZMod 2, ∀ g ∈ H.RX a b,
      lab a b (vm u) (s * g) = lab a b (vm u) g + v := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact ⟨lt_sq h (by norm_num) (by norm_num), _,
        fun g hg => lab_step h hc hvm (c := 0) (by norm_num) hg⟩
    · exact ⟨lt_sq h (by norm_num) (by norm_num), _,
        fun g hg => lab_step h hc hvm (c := 1) (by norm_num) hg⟩
    · exact ⟨lt_sq h (by norm_num) (by norm_num), _,
        fun g hg => lab_step h hc hvm (c := 2) (by norm_num) hg⟩
  have hmul : ∀ g ∈ H.RX a b, ∀ g' ∈ H.RX a b,
      lab a b (vm u) (g * g') = lab a b (vm u) g + lab a b (vm u) g' := by
    rw [hT]
    exact f_mul (lab_one h hc hvm) (by rw [← hT]; exact hS)
  have hRT : Rv a b u ≤ H.RX a b := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    have hx' : x ∈ (List.range (nr u)).map fun l => wE a b (RG u l) := hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx'
    rw [wE_of rfl]
    refine (H.RX a b).list_prod_mem fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    have hd' := RG_let u hu l (List.mem_range.1 hl) d hd
    exact lt_mem hd'.1 hd'.2
  have hRf : ∀ r ∈ Rv a b u, lab a b (vm u) r = 0 := by
    intro r hr
    refine Subgroup.closure_induction (p := fun g _ => lab a b (vm u) g = 0) (fun x hx => ?_)
      (lab_one h hc hvm) (fun x y hx hy ex ey => ?_) (fun x hx ex => ?_) hr
    · have hx' : x ∈ (List.range (nr u)).map fun l => wE a b (RG u l) := hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx'
      have hl' := List.mem_range.1 hl
      rw [wE_of rfl, lab_prod h hc hvm _ (RG_let u hu l hl')]
      exact RG_par u hu l hl'
    · rw [hmul x (hRT hx) y (hRT hy), ex, ey, add_zero]
    · have e := hmul x⁻¹ ((H.RX a b).inv_mem (hRT hx)) x (hRT hx)
      rw [inv_mul_cancel, lab_one h hc hvm, ex, add_zero] at e
      exact e.symm
  have hτf : lab a b (vm u) (lt a b (tau u)) = 1 := by
    rw [lab_lt h hc hvm ht2 ht5]
    exact hτ1
  obtain ⟨hiff, hcard⟩ := idx2 hT (lab_one h hc hvm) hS (lt_mem ht2 ht5) hτf (lt_sq h ht2 ht5)
    hRT hRf (hc_v h hu)
  refine ⟨hRT, hiff, hcard, by omega, lt_mem ht2 ht5, fun hm => ?_, lt_sq h ht2 ht5⟩
  have e := hRf _ hm
  rw [hτf] at e
  exact one_ne_zero e

end Group

end CFSG.KD.RuIdx2.Lab

end
