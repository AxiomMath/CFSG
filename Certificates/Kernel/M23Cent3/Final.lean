
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M23Check
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Sporadic.Schreier.M23PinnedInputs
public import Certificates.Kernel.M23Cent3.Checks
public import CFSG.Certificates.Kernel.ThreeChain.Sound
public import CFSG.Certificates.Kernel.ThreeChain.Words
public import CFSG.Certificates.Kernel.Enum.ZCHSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M23Base
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Enum.ZChkISound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Certificates.Kernel.Spor.PRecSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Spec
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23

set_option maxRecDepth 400000

public section

namespace CFSG.KD.M23Cent3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KC.ThreeChain CFSG.KC.OrbRow Subgroup
open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23 (xW yW c1W c2W r0W r1W r2W h0W h1W h2W letG gA gB
  wordG_mem m23_sylow)
open CFSG.Sporadic.Th (wordG)
open CFSG.Blueprint (NativeSporadic.M23)

local notation "⟪" w "⟫" => wordG letG w

@[expose] def invWg : List ℤ :=
  [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1]

abbrev Cx : Subgroup (Equiv.Perm (Fin 23)) :=
  NativeSporadic.M23 ⊓ Subgroup.centralizer ({⟪xW⟫} : Set (Equiv.Perm (Fin 23)))

theorem sB12641 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bA12641 {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true :=
  (bAnd_iff a b).1 h

theorem bIfT12641 {c t e : Bool} (h : bIf(c, t, e) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

theorem bIfF12641 {c t e : Bool} (h : bIf(c, t, e) = true) (hc : c = false) : e = true := by
  subst hc
  exact h

theorem pinA : PRep 23 5 (GN 0) gA := by unfold PRep; decide +kernel
theorem pinB : PRep 23 5 (GN 1) gB := by unfold PRep; decide +kernel
theorem pinAi : PRep 23 5 (GN 2) gA⁻¹ := by unfold PRep; decide +kernel
theorem pinBi : PRep 23 5 (GN 3) gB⁻¹ := by unfold PRep; decide +kernel
theorem pinX : PRep 23 5 (EL 0) ⟪xW⟫ := by unfold PRep; decide +kernel
theorem pinY : PRep 23 5 (EL 1) ⟪yW⟫ := by unfold PRep; decide +kernel
theorem pinC1 : PRep 23 5 (EL 2) ⟪c1W⟫ := by unfold PRep; decide +kernel
theorem pinC2 : PRep 23 5 (EL 3) ⟪c2W⟫ := by unfold PRep; decide +kernel
theorem pinR0 : PRep 23 5 (EL 4) ⟪r0W⟫ := by unfold PRep; decide +kernel
theorem pinR1 : PRep 23 5 (EL 5) ⟪r1W⟫ := by unfold PRep; decide +kernel
theorem pinR2 : PRep 23 5 (EL 6) ⟪r2W⟫ := by unfold PRep; decide +kernel

theorem canon_id12641 : canonK 23 5 (mask 5) (23 * 5) (pidn 23 5) = true := by decide +kernel

theorem prep_id12641 : PRep 23 5 (pidn 23 5) 1 := prep_pidn (by norm_num) (by norm_num)

theorem m23_eq_closure : NativeSporadic.M23 = closure ({gA, gB} : Set (Equiv.Perm (Fin 23))) :=
  rfl

theorem wW_mem23 (W L : Nat) : wW gA gB W L ∈ NativeSporadic.M23 := by
  rw [m23_eq_closure]
  exact wW_mem gA gB W L

theorem wp_eq12641 (W L q : Nat) (hq : q < 23) : wp W L q = (wW gA gB W L ⟨q, hq⟩ : Nat) :=
  wpt_prep_wW pinA pinAi pinB pinBi q hq

theorem wperm_prep12641 (W L : Nat) :
    PRep 23 5 (wperm 23 5 (mask 5) (GN 0) (GN 1) (GN 2) (GN 3) W L) (wW gA gB W L) :=
  wperm_prep_wW (by norm_num) (by norm_num) pinA pinAi pinB pinBi

@[expose] def pick2 {α : Type} (a b : α) (j : ℕ) : α := if j = 0 then a else b

theorem image_pick2 {α : Type} (a b : α) : pick2 a b '' {j | j < 2} = {a, b} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem pinH0 : PRep 23 5 (EL 7) ⟪h0W⟫ := by unfold PRep; decide +kernel
theorem pinH1 : PRep 23 5 (EL 8) ⟪h1W⟫ := by unfold PRep; decide +kernel
theorem pinH2 : PRep 23 5 (EL 9) ⟪h2W⟫ := by unfold PRep; decide +kernel
theorem pinG : PRep 23 5 (EL 10) ⟪invWg⟫ := by unfold PRep; decide +kernel

theorem el_facts {j : Nat} (hj : j < 11) : canonK 23 5 (mask 5) (23 * 5) (EL j) = true ∧
    canonK 23 5 (mask 5) (23 * 5) (EI j) = true ∧
    invEqK 23 5 (mask 5) (23 * 5) (EL j) (EI j) = true := by
  have h := ch12641_el
  simp only [bAnd_iff] at h
  have h1 := allN_spec h.2.2 j hj
  unfold elK invK cK at h1
  simp only [bAnd_iff] at h1
  exact h1.1

theorem prep_inv12641 {P Q : Nat} {σ : Equiv.Perm (Fin 23)} (hP : PRep 23 5 P σ)
    (h : invEqK 23 5 (mask 5) (23 * 5) P Q = true) : PRep 23 5 Q σ⁻¹ := by
  obtain ⟨-, -, h3⟩ := permOK_facts h
  intro x
  have e := (h3 _ (σ⁻¹ x).2).2
  have hs : σ (σ⁻¹ x) = x := by simp
  rw [hP (σ⁻¹ x), hs] at e
  exact e

theorem beq_self12641 (a : Nat) : Nat.beq a a = true := Eq.mpr (Nat.beq_eq_true_eq a a) rfl

theorem ne_of_beq12641 {p q : Nat} {σ τ : Equiv.Perm (Fin 23)}
    (cp : canonK 23 5 (mask 5) (23 * 5) p = true) (cq : canonK 23 5 (mask 5) (23 * 5) q = true)
    (hp : PRep 23 5 p σ) (hq : PRep 23 5 q τ) (e : Nat.beq p q = false) : σ ≠ τ := by
  intro h
  rw [h] at hp
  rw [code_eq_of_prep cp cq hp hq, beq_self12641] at e
  exact Bool.noConfusion e

theorem pinXi : PRep 23 5 (EI 0) ⟪xW⟫⁻¹ := prep_inv12641 pinX (el_facts (j := 0) (by norm_num)).2.2

theorem x_fix : ∀ i : Fin 23, ⟪xW⟫ i = i ↔ i ∈ ({0, 1, 2, 10, 15} : Finset (Fin 23)) := by
  have hF : ∀ i : Fin 23, inF i = true ↔ i ∈ ({0, 1, 2, 10, 15} : Finset (Fin 23)) := by
    decide +kernel
  intro i
  have h := allN_spec ch12641_fix i i.2
  unfold fxK at h
  rw [← hF i]
  have hx := pinX i
  cases hb : Nat.beq (pg 5 (mask 5) (EL 0) i) i
  · have h' := bIfF12641 h hb
    have hne : ((⟪xW⟫ i : Fin 23) : ℕ) ≠ i := fun e => by
      rw [hx, e, beq_self12641] at hb
      exact Bool.noConfusion hb
    constructor
    · intro e
      exact absurd (congrArg Fin.val e) hne
    · intro hin
      exact absurd (bIfT12641 h' hin) Bool.false_ne_true
  · exact ⟨fun _ => bIfT12641 h hb, fun _ => Fin.ext (hx.symm.trans (Nat.eq_of_beq_eq_true hb))⟩

theorem inv_facts12641 : ⟪invWg⟫ * ⟪xW⟫ * ⟪invWg⟫⁻¹ = ⟪xW⟫⁻¹ ∧ ⟪xW⟫⁻¹ ≠ ⟪xW⟫ := by
  have h := ch12641_inv
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have e := CFSG.KC.EnumSound.eq22_prep h1 pinG pinX pinXi pinG
  refine ⟨by rw [e]; group, ?_⟩
  have hb : Nat.beq (EL 0) (EI 0) = false := by
    cases hc : Nat.beq (EL 0) (EI 0)
    · rfl
    · exact absurd (bIfT12641 h2 hc) Bool.false_ne_true
  obtain ⟨c0, ci0, -⟩ := el_facts (j := 0) (by norm_num)
  exact (ne_of_beq12641 c0 ci0 pinX pinXi hb).symm

theorem inv_conj : ⟪invWg⟫ * ⟪xW⟫ * ⟪invWg⟫⁻¹ = ⟪xW⟫⁻¹ := inv_facts12641.1

theorem x_inv_ne : ⟪xW⟫⁻¹ ≠ ⟪xW⟫ := inv_facts12641.2

theorem comm_all : cmK (EL 2) (EL 0) = true ∧ cmK (EL 3) (EL 0) = true ∧
    cmK (EL 4) (EL 0) = true ∧ cmK (EL 5) (EL 0) = true ∧ cmK (EL 6) (EL 0) = true ∧
    cmK (EL 7) (EL 0) = true ∧ cmK (EL 8) (EL 0) = true ∧ cmK (EL 9) (EL 0) = true := by
  have h := ch12641_comm
  simp only [bAnd_iff] at h
  exact h

theorem mem_of_cm {p : Nat} {σ : Equiv.Perm (Fin 23)} (hp : PRep 23 5 p σ)
    (hm : σ ∈ NativeSporadic.M23) (h : cmK p (EL 0) = true) : σ ∈ Cx := by
  have e := CFSG.KC.EnumSound.eq22_prep h hp pinX pinX hp
  refine mem_inf.2 ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  first
  | exact e
  | exact e.symm

theorem c1_mem : ⟪c1W⟫ ∈ Cx := mem_of_cm pinC1 (wordG_mem _) comm_all.1
theorem c2_mem : ⟪c2W⟫ ∈ Cx := mem_of_cm pinC2 (wordG_mem _) comm_all.2.1
theorem h0_mem : ⟪h0W⟫ ∈ Cx := mem_of_cm pinH0 (wordG_mem _) comm_all.2.2.2.2.2.1
theorem h1_mem : ⟪h1W⟫ ∈ Cx := mem_of_cm pinH1 (wordG_mem _) comm_all.2.2.2.2.2.2.1
theorem h2_mem : ⟪h2W⟫ ∈ Cx := mem_of_cm pinH2 (wordG_mem _) comm_all.2.2.2.2.2.2.2

theorem wit_of {r h : Nat} (hr : r < 11) (hh : h < 11) {ρ η : Equiv.Perm (Fin 23)}
    (pr : PRep 23 5 (EL r) ρ) (ph : PRep 23 5 (EL h) η) (hw : witK r h = true) :
    (ρ * (η * ρ * η⁻¹)) ^ 3 = 1 ∧ ρ * (η * ρ * η⁻¹) ≠ 1 := by
  obtain ⟨cr, -, -⟩ := el_facts hr
  obtain ⟨ch, chi, hi⟩ := el_facts hh
  have phi := prep_inv12641 ph hi
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have pz : PRep 23 5 (pc (EL r) (pc (EL h) (pc (EL r) (EI h)))) (ρ * (η * ρ * η⁻¹)) := by
    have e : ρ * (η * (ρ * η⁻¹)) = ρ * (η * ρ * η⁻¹) := by group
    rw [← e]
    exact prep_pcomp hn pr (prep_pcomp hn ph (prep_pcomp hn pr phi))
  have cz := CFSG.KC.BfsPin.canonK_pcomp cr
    (CFSG.KC.BfsPin.canonK_pcomp ch (CFSG.KC.BfsPin.canonK_pcomp cr chi))
  unfold witK at hw
  rw [sB12641] at hw
  cases hz : Nat.beq (pc (EL r) (pc (EL h) (pc (EL r) (EI h)))) idK
  · have h3 := Nat.eq_of_beq_eq_true (bIfF12641 hw hz)
    have p3 : PRep 23 5 (pc (pc (EL r) (pc (EL h) (pc (EL r) (EI h))))
        (pc (pc (EL r) (pc (EL h) (pc (EL r) (EI h)))) (pc (EL r) (pc (EL h) (pc (EL r) (EI h))))))
        (ρ * (η * ρ * η⁻¹) * (ρ * (η * ρ * η⁻¹) * (ρ * (η * ρ * η⁻¹)))) :=
      prep_pcomp hn pz (prep_pcomp hn pz pz)
    rw [h3] at p3
    refine ⟨?_, ne_of_beq12641 cz canon_id12641 pz prep_id12641 hz⟩
    rw [pow_three]
    exact CFSG.KC.OrbGroup.prep_eq p3 prep_id12641
  · exact absurd (bIfT12641 hw hz) Bool.false_ne_true

theorem ord_all : witK 4 7 = true ∧ witK 5 8 = true ∧ witK 6 9 = true := by
  have h := ch12641_ord
  simp only [bAnd_iff] at h
  exact h.2.2.2

theorem wit0 : (⟪r0W⟫ * (⟪h0W⟫ * ⟪r0W⟫ * ⟪h0W⟫⁻¹)) ^ 3 = 1 ∧
    ⟪r0W⟫ * (⟪h0W⟫ * ⟪r0W⟫ * ⟪h0W⟫⁻¹) ≠ 1 :=
  wit_of (by norm_num) (by norm_num) pinR0 pinH0 ord_all.1

theorem wit1 : (⟪r1W⟫ * (⟪h1W⟫ * ⟪r1W⟫ * ⟪h1W⟫⁻¹)) ^ 3 = 1 ∧
    ⟪r1W⟫ * (⟪h1W⟫ * ⟪r1W⟫ * ⟪h1W⟫⁻¹) ≠ 1 :=
  wit_of (by norm_num) (by norm_num) pinR1 pinH1 ord_all.2.1

theorem wit2 : (⟪r2W⟫ * (⟪h2W⟫ * ⟪r2W⟫ * ⟪h2W⟫⁻¹)) ^ 3 = 1 ∧
    ⟪r2W⟫ * (⟪h2W⟫ * ⟪r2W⟫ * ⟪h2W⟫⁻¹) ≠ 1 :=
  wit_of (by norm_num) (by norm_num) pinR2 pinH2 ord_all.2.2

theorem three_dvd_of {z : Equiv.Perm (Fin 23)} (h : z ^ 3 = 1 ∧ z ≠ 1) : 3 ∣ orderOf z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [orderOf_eq_prime h.1 h.2]

theorem wits : ∀ p ∈ [(r0W, h0W), (r1W, h1W), (r2W, h2W)], ⟪p.2⟫ ∈ Cx ∧
    3 ∣ orderOf (⟪p.1⟫ * (⟪p.2⟫ * ⟪p.1⟫ * ⟪p.2⟫⁻¹)) := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨h0_mem, three_dvd_of wit0⟩
  · exact ⟨h1_mem, three_dvd_of wit1⟩
  · exact ⟨h2_mem, three_dvd_of wit2⟩

@[expose] def bpt (i : ℕ) : Fin 23 := ([0, 1, 2, 10, 15] : List (Fin 23)).getD i 0

@[expose] def Nl (i : ℕ) : ℕ := [23, 22, 21, 20, 16].getD i 0

noncomputable def lvS (l : ℕ) : List (Equiv.Perm (Fin 23)) :=
  (List.range (Nl l)).map fun k => wW gA gB (TW (23 * l + k)) (TL (23 * l + k))

theorem lvK_spec {l N b k : Nat} {f : Nat → Nat → Bool} (h : lvK l N b f k = true) :
    (k + 1 = N → PT (23 * l + k) < 23) ∧ (k + 1 ≠ N → PT (23 * l + k) < PT (23 * l + k + 1)) ∧
    wp (TW (23 * l + k)) (TL (23 * l + k)) b = PT (23 * l + k) ∧
    f (TW (23 * l + k)) (TL (23 * l + k)) = true := by
  unfold lvK at h
  simp only [sB12641] at h
  obtain ⟨h1, h2⟩ := bA12641 h
  obtain ⟨h3, h4⟩ := bA12641 h2
  refine ⟨fun hk => ?_, fun hk => ?_, Nat.eq_of_beq_eq_true h3, h4⟩
  · have e : Nat.beq (Nat.succ k) N = true := Nat.beq_eq_true_eq _ _ ▸ hk
    exact Nat.blt_eq.mp (bIfT12641 h1 e)
  · have e : Nat.beq (Nat.succ k) N = false := Bool.eq_false_iff.2 fun h => hk (Nat.eq_of_beq_eq_true h)
    exact Nat.blt_eq.mp (bIfF12641 h1 e)

theorem lv_all : (∀ k < 23, lvK 0 23 0 (fun _ _ => true) k = true) ∧
    (∀ k < 22, lvK 1 22 1 (fun W L => fx1 0 W L) k = true) ∧
    (∀ k < 21, lvK 2 21 2 (fun W L => bAnd(fx1 0 W L, fx1 1 W L)) k = true) ∧
    (∀ k < 20, lvK 3 20 10 (fun W L => bAnd(fx1 0 W L, bAnd(fx1 1 W L, fx1 2 W L))) k = true) ∧
    (∀ k < 16, lvK 4 16 15 (fun W L =>
      bAnd(fx1 0 W L, bAnd(fx1 1 W L, bAnd(fx1 2 W L, fx1 10 W L)))) k = true) := by
  have h := ch12641_lv
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨allN_spec h0, allN_spec h1, allN_spec h2, allN_spec h3, allN_spec h4⟩

theorem fx_of {p W L : Nat} (hp : p < 23) (h : fx1 p W L = true) :
    wW gA gB W L ⟨p, hp⟩ = ⟨p, hp⟩ :=
  Fin.ext ((wp_eq12641 W L p hp).symm.trans (Nat.eq_of_beq_eq_true h))

theorem level_entry {l k : ℕ} (hl : l < 5) (hk : k < Nl l) :
    (k + 1 = Nl l → PT (23 * l + k) < 23) ∧
      (k + 1 ≠ Nl l → PT (23 * l + k) < PT (23 * l + k + 1)) ∧
      wp (TW (23 * l + k)) (TL (23 * l + k)) (bpt l) = PT (23 * l + k) ∧
      ∀ j < l, wW gA gB (TW (23 * l + k)) (TL (23 * l + k)) (bpt j) = bpt j := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := lv_all
  interval_cases l
  · obtain ⟨e1, e2, e3, -⟩ := lvK_spec (a0 k hk)
    exact ⟨e1, e2, e3, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  · obtain ⟨e1, e2, e3, e4⟩ := lvK_spec (a1 k hk)
    refine ⟨e1, e2, e3, fun j hj => ?_⟩
    interval_cases j
    exact fx_of (by norm_num) e4
  · obtain ⟨e1, e2, e3, e4⟩ := lvK_spec (a2 k hk)
    obtain ⟨f0, f1⟩ := bA12641 e4
    refine ⟨e1, e2, e3, fun j hj => ?_⟩
    interval_cases j
    · exact fx_of (by norm_num) f0
    · exact fx_of (by norm_num) f1
  · obtain ⟨e1, e2, e3, e4⟩ := lvK_spec (a3 k hk)
    obtain ⟨f0, f⟩ := bA12641 e4
    obtain ⟨f1, f2⟩ := bA12641 f
    refine ⟨e1, e2, e3, fun j hj => ?_⟩
    interval_cases j
    · exact fx_of (by norm_num) f0
    · exact fx_of (by norm_num) f1
    · exact fx_of (by norm_num) f2
  · obtain ⟨e1, e2, e3, e4⟩ := lvK_spec (a4 k hk)
    obtain ⟨f0, f⟩ := bA12641 e4
    obtain ⟨f1, f⟩ := bA12641 f
    obtain ⟨f2, f3⟩ := bA12641 f
    refine ⟨e1, e2, e3, fun j hj => ?_⟩
    interval_cases j
    · exact fx_of (by norm_num) f0
    · exact fx_of (by norm_num) f1
    · exact fx_of (by norm_num) f2
    · exact fx_of (by norm_num) f3

theorem level_lt {l : ℕ} (hl : l < 5) : ∀ k < Nl l, PT (23 * l + k) < 23 := by
  have key : ∀ d k, k + d + 1 = Nl l → PT (23 * l + k) < 23 := by
    intro d
    induction d with
    | zero => intro k hk; exact (level_entry hl (by omega)).1 (by omega)
    | succ d ih =>
      intro k hk
      exact lt_trans ((level_entry hl (by omega)).2.1 (by omega)) (ih (k + 1) (by omega))
  intro k hk
  exact key (Nl l - k - 1) k (by omega)

theorem level_mono {l : ℕ} (hl : l < 5) :
    ∀ a b, a < b → b < Nl l → PT (23 * l + a) < PT (23 * l + b) := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | h1
    · exact (ih h1 (by omega)).trans ((level_entry hl (by omega)).2.1 (by omega))
    · subst h1
      exact (level_entry hl (by omega)).2.1 (by omega)

theorem lvS_mem {l : ℕ} (hl : l < 5) {s : Equiv.Perm (Fin 23)} (hs : s ∈ lvS l) :
    s ∈ NativeSporadic.M23 ∧ ∀ j < l, s (bpt j) = bpt j := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hs
  exact ⟨wW_mem23 _ _, (level_entry hl (List.mem_range.1 hk)).2.2.2⟩

theorem lvS_orbit {l : ℕ} (hl : l < 5) :
    Nl l ≤ Nat.card {y : Fin 23 // ∃ g ∈ closure {g | g ∈ lvS l}, g • bpt l = y} := by
  have hpt : ∀ k : Fin (Nl l), PT (23 * l + k) < 23 := fun k => level_lt hl k k.2
  let f : Fin (Nl l) → {y : Fin 23 // ∃ g ∈ closure {g | g ∈ lvS l}, g • bpt l = y} :=
    fun k => ⟨⟨PT (23 * l + k), hpt k⟩, wW gA gB (TW (23 * l + k)) (TL (23 * l + k)),
      subset_closure (List.mem_map.2 ⟨k, List.mem_range.2 k.2, rfl⟩), by
        rw [Equiv.Perm.smul_def]
        exact Fin.ext ((wp_eq12641 _ _ _ (bpt l).2).symm.trans (level_entry hl k.2).2.2.1)⟩
  have hf : Function.Injective f := by
    intro a b e
    have e' : PT (23 * l + a) = PT (23 * l + b) := congrArg (fun y => (y.1 : ℕ)) e
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e' (Nat.ne_of_lt (level_mono hl a b h b.2))
    · exact Fin.ext h
    · exact absurd e'.symm (Nat.ne_of_lt (level_mono hl b a h a.2))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem stab_card_le :
    Nat.card (stabB NativeSporadic.M23 bpt 5) ≤ 3 := by
  have h := card_fix_mul_le NativeSporadic.M23 bpt 5 lvS Nl (fun i hi s hs => lvS_mem hi hs)
    (fun i hi => lvS_orbit hi)
  rw [CFSG.Sporadic.Schreier.m23_card] at h
  have e : ∏ i ∈ Finset.range 5, Nl i = 3400320 := by decide +kernel
  rw [e] at h
  exact Nat.le_of_mul_le_mul_right (h.trans (le_of_eq (by norm_num))) (by norm_num)

theorem cent_card_le : Nat.card Cx ≤ 180 := by
  have hF : ∀ a, a ∈ ((({0, 1, 2, 10, 15} : Finset (Fin 23))) : Set (Fin 23)) ↔
      ∃ t < 5, bpt t = a := by
    intro a
    rw [Finset.mem_coe]
    revert a
    decide
  have e := stabB_eq_inf_fixing NativeSporadic.M23 bpt 5 _ hF
  have h := two_card_cent_le NativeSporadic.M23 (wordG_mem invWg) ({0, 1, 2, 10, 15} : Finset (Fin 23))
    x_fix inv_conj x_inv_ne
  rw [← e] at h
  have hs := stab_card_le
  have hc : ({0, 1, 2, 10, 15} : Finset (Fin 23)).card.factorial = 120 := by decide
  rw [hc] at h
  change 2 * Nat.card Cx ≤ _ at h
  have : Nat.card (stabB NativeSporadic.M23 bpt 5) * 120 ≤ 360 := by omega
  omega

theorem ce_bind : CE.G 0 = pidn 23 5 ∧ CE.G 1 = pidn 23 5 ∧ CE.GI 0 = EL 2 ∧ CE.GI 1 = EL 3 ∧
    CE.R = pidn 23 5 ∧ CE.cnt = 180 ∧ penumHdK CE.R CE.cnt 2000 CE.T CE.PL = true ∧
    S.G 0 = pidn 23 5 ∧ S.G 1 = pidn 23 5 ∧ S.GI 0 = EL 0 ∧ S.GI 1 = EL 1 ∧
    S.R = pidn 23 5 ∧ S.cnt = 9 ∧ penumHdK S.R S.cnt 100 S.T S.PL = true := by
  have h := ch12641_bind
  simp only [bAnd_iff] at h
  obtain ⟨-, g0, g1, i0, i1, r, c, hd, -, sg0, sg1, si0, si1, sr, sc, shd, -⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true g0, Nat.eq_of_beq_eq_true g1, Nat.eq_of_beq_eq_true i0,
    Nat.eq_of_beq_eq_true i1, Nat.eq_of_beq_eq_true r, Nat.eq_of_beq_eq_true c, hd,
    Nat.eq_of_beq_eq_true sg0, Nat.eq_of_beq_eq_true sg1, Nat.eq_of_beq_eq_true si0,
    Nat.eq_of_beq_eq_true si1, Nat.eq_of_beq_eq_true sr, Nat.eq_of_beq_eq_true sc, shd⟩

theorem ce_pt : ∀ i < CE.cnt, penumPtK 23 5 (mask 5) (23 * 5) true CE.G CE.GI 2 CE.cnt CE.T CE.PL
    CE.POS CE.SRT CE.SRI i = true := by
  intro i hi
  have hc := ce_bind.2.2.2.2.2.1
  rw [hc] at hi
  have hs : ∀ s < 3, ceE s = true := by
    intro s hs
    interval_cases s
    · exact ch12641ceE_0
    · exact ch12641ceE_1
    · exact ch12641ceE_2
  exact CFSG.KS.PRec.penumSlK_pt (hs (i / 60) (by omega)) (i := i)
    (by change i / 60 * 60 ≤ i; exact Nat.div_mul_le_self i 60)
    (by change i < i / 60 * 60 + 60; omega) (by rw [hc]; exact hi)

theorem ce_group : ∃ e : ℕ → Equiv.Perm (Fin 23), (∀ i < 180, PRep 23 5 (CE.T i) (e i)) ∧
    (∀ a < 180, ∀ b < 180, e a = e b → a = b) ∧
    (∀ y, y ∈ closure ({⟪c1W⟫, ⟪c2W⟫} : Set (Equiv.Perm (Fin 23))) ↔ ∃ i < 180, e i = y) ∧
    Nat.card (closure ({⟪c1W⟫, ⟪c2W⟫} : Set (Equiv.Perm (Fin 23)))) = 180 := by
  obtain ⟨g0, g1, i0, i1, r, c, hd, -⟩ := ce_bind
  have hG : ∀ j < 2, CE.G j = pidn 23 5 := by
    intro j hj
    interval_cases j
    · exact g0
    · exact g1
  have hg : ∀ j < 2, PRep 23 5 (CE.GI j) (pick2 ⟪c1W⟫ ⟪c2W⟫ j) := by
    intro j hj
    interval_cases j
    · rw [i0]; exact pinC1
    · rw [i1]; exact pinC2
  rw [r] at hd
  have h := penumRight_group (by norm_num) (by norm_num) hG hg hd ce_pt
  rw [image_pick2, c] at h
  exact h

theorem cent_eq :
    closure ({⟪c1W⟫, ⟪c2W⟫} : Set (Equiv.Perm (Fin 23))) = Cx ∧ Nat.card Cx = 180 := by
  obtain ⟨-, -, -, -, hK⟩ := ce_group
  have hle : closure ({⟪c1W⟫, ⟪c2W⟫} : Set (Equiv.Perm (Fin 23))) ≤ Cx := by
    rw [closure_le]
    rintro g (rfl | rfl)
    · exact c1_mem
    · exact c2_mem
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hK]; exact cent_card_le)
  exact ⟨heq, by rw [← heq, hK]⟩

theorem selK_of {p : Nat} {y : Equiv.Perm (Fin 23)} (hp : canonK 23 5 (mask 5) (23 * 5) p = true)
    (hy : PRep 23 5 p y) (h1 : y ≠ 1) (hq : y ^ 2 = 1 ∨ y ^ 5 = 1) : selK p = true := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hne : Nat.beq p idK = false := Bool.eq_false_iff.2 fun h =>
    h1 (CFSG.KC.OrbGroup.prep_eq hy (by rw [Nat.eq_of_beq_eq_true h]; exact prep_id12641))
  have h2 : PRep 23 5 (pc p p) (y * y) := prep_pcomp hn hy hy
  have c2 := CFSG.KC.BfsPin.canonK_pcomp hp hp
  unfold selK
  rw [hne, sB12641]
  rcases hq with hq | hq
  · have e : pc p p = idK := code_eq_of_prep c2 canon_id12641 h2 (by
      rw [← pow_two, hq]; exact prep_id12641)
    rw [e]
    rfl
  · have h5 : PRep 23 5 (pc (pc (pc p p) (pc p p)) p) (y * y * (y * y) * y) :=
      prep_pcomp hn (prep_pcomp hn h2 h2) hy
    have e : pc (pc (pc p p) (pc p p)) p = idK :=
      code_eq_of_prep (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp c2 c2) hp)
        canon_id12641 h5 (by
        have : y * y * (y * y) * y = y ^ 5 := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [this, hq]
        exact prep_id12641)
    change bIf(Nat.beq (pc p p) idK, true, Nat.beq (pc (pc (pc p p) (pc p p)) p) idK) = true
    rw [e]
    cases Nat.beq (pc p p) idK <;> rfl

theorem cv_all : ∀ i < 180, cvK i = true := by
  intro i hi
  have hs : ∀ s < 3, cv s = true := by
    intro s hs
    interval_cases s
    · exact ch12641cv_0
    · exact ch12641cv_1
    · exact ch12641cv_2
  have h := allBlk_spec (hs (i / 60) (by omega)) (i % 60) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 60) 60) (i % 60) = i := by
    change i / 60 * 60 + i % 60 = i
    omega
  rwa [e] at h

theorem prime_dvd_180 {q : ℕ} (hq : q.Prime) (hd : q ∣ 180) (h3 : q ≠ 3) : q = 2 ∨ q = 5 := by
  rw [show (180 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hq).1 hd with h | h5
  · rcases (Nat.Prime.dvd_mul hq).1 h with h2 | h3'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h3')) h3
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).1 h5)

theorem rows_cover : ∀ y ∈ Cx, (orderOf y).Prime →
    orderOf y ≠ 3 → ∃ r ∈ [r0W, r1W, r2W], ∃ c ∈ Cx, y = c * ⟪r⟫ * c⁻¹ := by
  intro y hy hq hq3
  obtain ⟨e, he, -, hmem, -⟩ := ce_group
  obtain ⟨heq, hcard⟩ := cent_eq
  obtain ⟨i, hi, rfl⟩ := (hmem y).1 (heq ▸ hy)
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hci : ∀ i < 180, canonK 23 5 (mask 5) (23 * 5) (CE.T i) = true := fun i hi =>
    (penumPt_specH (ce_pt i (by rw [ce_bind.2.2.2.2.2.1]; exact hi))).1
  have hdvd : orderOf (e i) ∣ 180 := by
    rw [← hcard, ← Subgroup.orderOf_mk (e i) hy]
    exact orderOf_dvd_natCard _
  have h1 : e i ≠ 1 := fun h => by rw [h, orderOf_one] at hq; exact Nat.not_prime_one hq
  have hpow : e i ^ 2 = 1 ∨ e i ^ 5 = 1 := by
    rcases prime_dvd_180 hq hdvd hq3 with h | h
    · exact Or.inl (h ▸ pow_orderOf_eq_one (e i))
    · exact Or.inr (h ▸ pow_orderOf_eq_one (e i))
  have hsel := selK_of (hci i hi) (he i hi) h1 hpow
  have hcv := cv_all i hi
  unfold cvK at hcv
  rw [sB12641, hsel] at hcv
  simp only [sB12641] at hcv
  obtain ⟨hj, h⟩ := bA12641 hcv
  obtain ⟨hk, h⟩ := bA12641 h
  have hj' := Nat.blt_eq.mp hj
  have hk' : Nat.shiftRight (Cv i) 16 < 180 := by
    rw [← ce_bind.2.2.2.2.2.1]; exact Nat.blt_eq.mp hk
  set j := Nat.land (Cv i) 65535
  set k := Nat.shiftRight (Cv i) 16
  have hr : ∃ r ∈ [r0W, r1W, r2W], PRep 23 5 (EL (Nat.add 4 j)) ⟪r⟫ := by
    interval_cases j
    · exact ⟨r0W, by simp, pinR0⟩
    · exact ⟨r1W, by simp, pinR1⟩
    · exact ⟨r2W, by simp, pinR2⟩
  obtain ⟨r, hrm, hrp⟩ := hr
  have hc := CFSG.KC.EnumSound.eq22_prep h (he i hi) (he k hk') (he k hk') hrp
  refine ⟨r, hrm, e k, heq ▸ (hmem (e k)).2 ⟨k, hk', rfl⟩, ?_⟩
  calc e i = e i * e k * (e k)⁻¹ := by group
    _ = e k * ⟪r⟫ * (e k)⁻¹ := by rw [hc]

theorem s_pt : ∀ i < S.cnt, penumPtK 23 5 (mask 5) (23 * 5) true S.G S.GI 2 S.cnt S.T S.PL
    S.POS S.SRT S.SRI i = true := fun i hi =>
  CFSG.KS.PRec.penumSlK_pt ch12641sE (Nat.zero_le i) (by omega) hi

theorem s_group : ∃ e : ℕ → Equiv.Perm (Fin 23), (∀ i < 9, PRep 23 5 (S.T i) (e i)) ∧
    (∀ y, y ∈ closure ({⟪xW⟫, ⟪yW⟫} : Set (Equiv.Perm (Fin 23))) ↔ ∃ i < 9, e i = y) ∧
    Nat.card (closure ({⟪xW⟫, ⟪yW⟫} : Set (Equiv.Perm (Fin 23)))) = 9 := by
  obtain ⟨-, -, -, -, -, -, -, g0, g1, i0, i1, r, c, hd⟩ := ce_bind
  have hG : ∀ j < 2, S.G j = pidn 23 5 := by
    intro j hj
    interval_cases j
    · exact g0
    · exact g1
  have hg : ∀ j < 2, PRep 23 5 (S.GI j) (pick2 ⟪xW⟫ ⟪yW⟫ j) := by
    intro j hj
    interval_cases j
    · rw [i0]; exact pinX
    · rw [i1]; exact pinY
  rw [r] at hd
  obtain ⟨e, he, -, hmem, hcard⟩ := penumRight_group (by norm_num) (by norm_num) hG hg hd s_pt
  rw [image_pick2, c] at hmem hcard
  rw [c] at he
  exact ⟨e, he, hmem, hcard⟩

theorem m23_conj_x : ∀ t ∈ NativeSporadic.M23, orderOf t = 3 →
    ∃ g ∈ NativeSporadic.M23, t = g * ⟪xW⟫ * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he, hmem, hcard⟩ := s_group
  have hPG : closure ({⟪xW⟫, ⟪yW⟫} : Set (Equiv.Perm (Fin 23))) ≤ NativeSporadic.M23 := by
    rw [closure_le]
    rintro g (rfl | rfl)
    · exact wordG_mem _
    · exact wordG_mem _
  have hP : Nat.card (closure ({⟪xW⟫, ⟪yW⟫} : Set (Equiv.Perm (Fin 23)))) =
      3 ^ (Nat.card NativeSporadic.M23).factorization 3 := by
    rw [hcard, CFSG.Sporadic.Schreier.m23_card]
    exact m23_sylow
  refine conj_cover_of_sylow NativeSporadic.M23 _ hPG hP fun s hs hs3 => ?_
  obtain ⟨i, hi, rfl⟩ := (hmem s).1 hs
  have hi' : i < S.cnt := by rw [ce_bind.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hi
  have hsyl := allN_spec ch12641_syl i hi'
  unfold sylK at hsyl
  rw [sB12641] at hsyl
  have hne : Nat.beq (S.T i) idK = false := Bool.eq_false_iff.2 fun h => by
    have h1 : e i = 1 := CFSG.KC.OrbGroup.prep_eq (he i hi)
      (by rw [Nat.eq_of_beq_eq_true h]; exact prep_id12641)
    rw [h1, orderOf_one] at hs3
    exact absurd hs3 (by norm_num)
  have h := bIfF12641 hsyl hne
  simp only [sB12641] at h
  have hu := CFSG.KC.EnumSound.eq22_prep h (wperm_prep12641 (SW i) (SL i)) (he i hi) pinX
    (wperm_prep12641 (SW i) (SL i))
  refine ⟨(wW gA gB (SW i) (SL i))⁻¹, inv_mem (wW_mem23 _ _), ?_⟩
  calc e i = (wW gA gB (SW i) (SL i))⁻¹ * (wW gA gB (SW i) (SL i) * e i) := by group
    _ = (wW gA gB (SW i) (SL i))⁻¹ * ⟪xW⟫ * (wW gA gB (SW i) (SL i))⁻¹⁻¹ := by
      rw [hu]; group

open Certificates in
open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23 CFSG.Sporadic.Th CFSG.Blueprint Subgroup in
theorem m23_cent3_facts :
    (∀ t ∈ NativeSporadic.M23, orderOf t = 3 → ∃ g ∈ NativeSporadic.M23,
      t = g * wordG letG xW * g⁻¹) ∧
    closure {wordG letG c1W, wordG letG c2W} =
      NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23))) ∧
    Nat.card ↥(NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23)))) =
      180 ∧
    (∀ y ∈ NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23))),
      (orderOf y).Prime → orderOf y ≠ 3 → ∃ r ∈ [r0W, r1W, r2W],
        ∃ c ∈ NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23))),
          y = c * wordG letG r * c⁻¹) ∧
    ∀ p ∈ [(r0W, h0W), (r1W, h1W), (r2W, h2W)],
      wordG letG p.2 ∈
        NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23))) ∧
      3 ∣ orderOf (wordG letG p.1 * (wordG letG p.2 * wordG letG p.1 * (wordG letG p.2)⁻¹)) :=
  ⟨m23_conj_x, cent_eq.1, cent_eq.2, rows_cover, wits⟩

end CFSG.KD.M23Cent3

end
