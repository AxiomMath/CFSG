module

public import Certificates.Kernel.HN1408.TabXCntFacts
public import Certificates.Kernel.HN1408.TabXRecChk
public import Certificates.Kernel.HN1408.TabXRecCnt
public import Certificates.Kernel.HN1408.TableIGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKSpec
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Enum

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TabX

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.BaseEq CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog

section Abstract

variable {G : Type} [Group G]

theorem mul_inv_mem_of_mul_mem [DecidableEq G] {E : Finset G} {x : G}
    (hx : ∀ y ∈ E, y * x ∈ E) : ∀ y ∈ E, y * x⁻¹ ∈ E := by
  have hsub : E.image (· * x) ⊆ E := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact hx y hy
  have hcard : (E.image (· * x)).card = E.card :=
    Finset.card_image_of_injective _ (mul_left_injective x)
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
  intro y hy
  rw [← heq] at hy
  obtain ⟨y', hy', e⟩ := Finset.mem_image.1 hy
  rw [← e, mul_inv_cancel_right]
  exact hy'

theorem rec_mem_iff {n k : ℕ} {e g : ℕ → G} {dep : ℕ → ℕ} (hn : 0 < n) (h0 : e 0 = 1)
    (htree : ∀ r < n, r ≠ 0 → ∃ p < n, ∃ l < k, dep r = dep p + 1 ∧ e r = e p * g l)
    (hcl : ∀ r < n, ∀ l < k, ∃ q < n, e q = e r * g l) (x : G) :
    x ∈ closure (g '' Set.Iio k) ↔ ∃ r < n, e r = x := by
  classical
  constructor
  · intro hx
    let E : Finset G := (Finset.range n).image e
    have hE : ∀ y, y ∈ E ↔ ∃ r < n, e r = y := by
      intro y
      simp only [E, Finset.mem_image, Finset.mem_range]
    have hg : ∀ l < k, ∀ y ∈ E, y * g l ∈ E := by
      intro l hl y hy
      obtain ⟨r, hr, rfl⟩ := (hE y).1 hy
      obtain ⟨q, hq, e'⟩ := hcl r hr l hl
      exact (hE _).2 ⟨q, hq, e'⟩
    let T : Subgroup G :=
      { carrier := {a | ∀ y ∈ E, y * a ∈ E}
        mul_mem' := fun {a b} ha hb y hy => by
          rw [← mul_assoc]
          exact hb _ (ha y hy)
        one_mem' := fun y hy => by
          rw [mul_one]
          exact hy
        inv_mem' := fun {a} ha => mul_inv_mem_of_mul_mem ha }
    have hle : closure (g '' Set.Iio k) ≤ T := by
      rw [closure_le]
      rintro _ ⟨l, hl, rfl⟩
      exact hg l hl
    have h1 : (1 : G) ∈ E := (hE 1).2 ⟨0, hn, h0⟩
    have h2 := hle hx 1 h1
    rw [one_mul] at h2
    exact (hE x).1 h2
  · rintro ⟨r, hr, rfl⟩
    suffices H : ∀ d r, dep r = d → r < n → e r ∈ closure (g '' Set.Iio k) from H _ r rfl hr
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro r hd hr
      by_cases hr0 : r = 0
      · rw [hr0, h0]
        exact one_mem _
      · obtain ⟨p, hp, l, hl, hdp, e'⟩ := htree r hr hr0
        rw [e']
        exact mul_mem (ih _ (by omega) p rfl hp) (subset_closure ⟨l, hl, rfl⟩)

theorem rec_ncard {n k : ℕ} {e g : ℕ → G}
    (hmem : ∀ x, x ∈ closure (g '' Set.Iio k) ↔ ∃ r < n, e r = x)
    (hinj : ∀ r s, r < n → s < n → e r = e s → r = s) {Q : G → Prop} {F : ℕ → Bool}
    (hQ : ∀ r < n, F r = true ↔ Q (e r)) :
    {x | x ∈ closure (g '' Set.Iio k) ∧ Q x}.ncard =
      ((Finset.range n).filter fun r => F r = true).card := by
  classical
  have hs : {x | x ∈ closure (g '' Set.Iio k) ∧ Q x} =
      e '' ↑((Finset.range n).filter fun r => F r = true) := by
    ext x
    simp only [Set.mem_setOf_eq, hmem, Set.mem_image, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hq⟩
      exact ⟨r, ⟨hr, (hQ r hr).2 hq⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hF⟩, rfl⟩
      exact ⟨⟨r, hr, rfl⟩, (hQ r hr).1 hF⟩
  have hi : Set.InjOn e ↑((Finset.range n).filter fun r => F r = true) := by
    intro r hr s hs' h
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hr hs'
    exact hinj r s hr.1 hs'.1 h
  rw [hs, hi.ncard_image, Set.ncard_coe_finset]

theorem rec_card {n k : ℕ} {e g : ℕ → G}
    (hmem : ∀ x, x ∈ closure (g '' Set.Iio k) ↔ ∃ r < n, e r = x)
    (hinj : ∀ r s, r < n → s < n → e r = e s → r = s) :
    Nat.card ↥(closure (g '' Set.Iio k)) = n := by
  have hc : Nat.card ↥(closure (g '' Set.Iio k)) =
      ((closure (g '' Set.Iio k) : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
  have hs : ((closure (g '' Set.Iio k) : Subgroup G) : Set G) =
      {x | x ∈ closure (g '' Set.Iio k) ∧ True} := by
    ext x
    simp
  rw [hc, hs, rec_ncard hmem hinj (F := fun _ => true) (fun _ _ => by simp)]
  simp

end Abstract

theorem strictB_x (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

noncomputable def elC (c : ℕ) : Equiv.Perm (Fin 1408) := t0P (c / 24) * t1P (c % 24)

theorem elC_mem (hP : Nat.card ↥P1408 = 177408000) {c : ℕ} (hc : c < 30720) :
    elC c ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
  CzInv.mem_cz hP (by omega) (Nat.mod_lt _ (by norm_num))

theorem elC_zero : elC 0 = 1 := by
  rw [elC, Nat.zero_div, Nat.zero_mod, t0P_zero_one, t1P_zero_one, one_mul]

theorem ev_elC {c x : ℕ} (hc : c < 30720) (hx : x < 1408) : ev c x = (elC c ⟨x, hx⟩).val := by
  have hi : c / 24 < 1280 := by omega
  rw [ev.eq_1]
  exact ev_eq hi (Nat.mod_lt _ (by norm_num)) hx

theorem ev_ev {c h x : ℕ} (hc : c < 30720) (hh : h < 30720) (hx : x < 1408) :
    ev c (ev h x) = ((elC c * elC h) ⟨x, hx⟩).val := by
  rw [ev_elC hh hx, ev_elC hc (Fin.isLt _)]
  rfl

theorem elC_inj {c c' : ℕ} (hc : c < 30720) (hc' : c' < 30720) (h : elC c = elC c') : c = c' := by
  obtain ⟨h1, h2⟩ := el_inj (by omega) (by omega) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) h
  omega

theorem eq_of_eqB (hP : Nat.card ↥P1408 = 177408000) {f₁ f₂ : ℕ → ℕ} {g h : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (hh : h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (h1 : ∀ x (hx : x < 1408), f₁ x = (g ⟨x, hx⟩).val)
    (h2 : ∀ x (hx : x < 1408), f₂ x = (h ⟨x, hx⟩).val) (e : eqB f₁ f₂ = true) : g = h := by
  unfold eqB at e
  obtain ⟨a, b⟩ := mkA e
  have a' := Nat.eq_of_beq_eq_true a
  have b' := Nat.eq_of_beq_eq_true b
  rw [h1 0 (by norm_num), h2 0 (by norm_num)] at a'
  rw [h1 1 (by norm_num), h2 1 (by norm_num)] at b'
  exact eq_of_base hP hg hh (Fin.ext a') (Fin.ext b')

theorem eqB_of_eq {f₁ f₂ : ℕ → ℕ} {g : Equiv.Perm (Fin 1408)}
    (h1 : ∀ x (hx : x < 1408), f₁ x = (g ⟨x, hx⟩).val)
    (h2 : ∀ x (hx : x < 1408), f₂ x = (g ⟨x, hx⟩).val) : eqB f₁ f₂ = true := by
  unfold eqB
  rw [h1 0 (by norm_num), h2 0 (by norm_num), h1 1 (by norm_num), h2 1 (by norm_num),
    Nat.beq_refl, Nat.beq_refl]

theorem elC_eq_mul (hP : Nat.card ↥P1408 = 177408000) {a b c : ℕ} (ha : a < 30720)
    (hb : b < 30720) (hc : c < 30720)
    (e : eqB (fun x => ev a x) (fun x => ev b (ev c x)) = true) : elC a = elC b * elC c :=
  eq_of_eqB hP (elC_mem hP ha) (mul_mem (elC_mem hP hb) (elC_mem hP hc))
    (fun _ hx => ev_elC ha hx) (fun _ hx => ev_ev hb hc hx) e

theorem commC_iff (hP : Nat.card ↥P1408 = 177408000) {c h : ℕ} (hc : c < 30720)
    (hh : h < 30720) : commC c h = true ↔ elC c * elC h = elC h * elC c := by
  unfold commC
  constructor
  · exact eq_of_eqB hP (mul_mem (elC_mem hP hc) (elC_mem hP hh))
      (mul_mem (elC_mem hP hh) (elC_mem hP hc)) (fun _ hx => ev_ev hc hh hx)
      (fun _ hx => ev_ev hh hc hx)
  · intro e
    exact eqB_of_eq (g := elC c * elC h) (fun _ hx => ev_ev hc hh hx)
      (fun _ hx => by rw [e]; exact ev_ev hh hc hx)

theorem recRow_parts {Rw : ℕ → ℕ} {n k : ℕ} {gc : ℕ → ℕ} {r : ℕ}
    (h : recRow Rw n k gc r = true) :
    cdOf Rw r < 30720 ∧ (r + 1 < n → cdOf Rw r < cdOf Rw (r + 1)) ∧ (r = 0 → cdOf Rw r = 0) ∧
      (r ≠ 0 → ∃ p l, p < n ∧ l < k ∧ fd (Rw r) 3 = fd (Rw p) 3 + 1 ∧
        eqB (fun x => ev (cdOf Rw r) x) (fun x => ev (cdOf Rw p) (ev (gc l) x)) = true) ∧
      (∀ l < k, ∃ q, q < n ∧
        eqB (fun x => ev (cdOf Rw q) x) (fun x => ev (cdOf Rw r) (ev (gc l) x)) = true) := by
  unfold recRow at h
  simp only [strictB_x] at h
  obtain ⟨hA, h⟩ := mkA h
  obtain ⟨hB, h⟩ := mkA h
  obtain ⟨hC, hD⟩ := mkA h
  refine ⟨Nat.blt_eq.mp hA, fun hr => ?_, fun hr => ?_, fun hr => ?_, fun l hl => ?_⟩
  · have e : Nat.blt (Nat.succ r) n = true := Nat.blt_eq.mpr hr
    rw [e] at hB
    exact Nat.blt_eq.mp hB
  · subst hr
    have e : Nat.beq 0 0 = true := rfl
    rw [e] at hC
    exact Nat.eq_of_beq_eq_true (mkA hC).1
  · have e0 : Nat.beq r 0 = false :=
      Bool.eq_false_iff.2 fun h'' => hr (Nat.eq_of_beq_eq_true h'')
    rw [e0] at hC
    obtain ⟨a, hC⟩ := mkA hC
    obtain ⟨b, hC⟩ := mkA hC
    obtain ⟨c, d⟩ := mkA hC
    exact ⟨_, _, Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.eq_of_beq_eq_true c, d⟩
  · have h' := allN_spec hD l hl
    obtain ⟨a, b⟩ := mkA h'
    exact ⟨_, Nat.blt_eq.mp a, b⟩

theorem rec_lt {Rw : ℕ → ℕ} {n k : ℕ} {gc : ℕ → ℕ} (hrow : ∀ r < n, recRow Rw n k gc r = true)
    {r s : ℕ} (h : r < s) (hs : s < n) : cdOf Rw r < cdOf Rw s := by
  induction s with
  | zero => omega
  | succ s ih =>
    have e := (recRow_parts (hrow s (by omega))).2.1 hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact (ih h' (by omega)).trans e
    · rw [h']
      exact e

theorem rec_facts (hP : Nat.card ↥P1408 = 177408000) {Rw : ℕ → ℕ} {n k : ℕ} {gc : ℕ → ℕ}
    (hn : 0 < n) (hrow : ∀ r < n, recRow Rw n k gc r = true) (hgc : ∀ l < k, gc l < 30720) :
    (∀ x, x ∈ closure ((fun l => elC (gc l)) '' Set.Iio k) ↔ ∃ r < n, elC (cdOf Rw r) = x) ∧
      Nat.card ↥(closure ((fun l => elC (gc l)) '' Set.Iio k)) = n := by
  have hcd : ∀ r < n, cdOf Rw r < 30720 := fun r hr => (recRow_parts (hrow r hr)).1
  have hinj : ∀ r s, r < n → s < n → elC (cdOf Rw r) = elC (cdOf Rw s) → r = s := by
    intro r s hr hs e
    have ec := elC_inj (hcd r hr) (hcd s hs) e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd ec (rec_lt hrow hlt hs).ne
    · exact absurd ec (rec_lt hrow hlt hr).ne'
  have hmem := rec_mem_iff (e := fun r => elC (cdOf Rw r)) (g := fun l => elC (gc l))
    (dep := fun r => fd (Rw r) 3) hn
    (by rw [(recRow_parts (hrow 0 hn)).2.2.1 rfl, elC_zero])
    (fun r hr hr0 => by
      obtain ⟨p, l, hp, hl, hd, e⟩ := (recRow_parts (hrow r hr)).2.2.2.1 hr0
      exact ⟨p, hp, l, hl, hd, elC_eq_mul hP (hcd r hr) (hcd p hp) (hgc l hl) e⟩)
    (fun r hr l hl => by
      obtain ⟨q, hq, e⟩ := (recRow_parts (hrow r hr)).2.2.2.2 l hl
      exact ⟨q, hq, elC_eq_mul hP (hcd q hq) (hcd r hr) (hgc l hl) e⟩)
  exact ⟨hmem, rec_card hmem hinj⟩

theorem ne_of_gapK {Rw : ℕ → ℕ} {n k : ℕ} {gc : ℕ → ℕ}
    (hrow : ∀ r < n, recRow Rw n k gc r = true) {c p : ℕ} (h : gapK (cdOf Rw) n c p = true) :
    ∀ r < n, cdOf Rw r ≠ c := by
  unfold gapK at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨d, h⟩ := mkA h
  have ha := Nat.le_of_ble_eq_true a
  have hb := Nat.le_of_ble_eq_true b
  have hd : cdOf Rw (p - 1) < c := Nat.blt_eq.mp d
  intro r hr e
  by_cases hrp : r < p
  · have hle : cdOf Rw r ≤ cdOf Rw (p - 1) := by
      rcases Nat.lt_or_ge r (p - 1) with h' | h'
      · exact (rec_lt hrow h' (by omega)).le
      · rw [show r = p - 1 by omega]
    omega
  · have hpn : Nat.beq p n = false :=
      Bool.eq_false_iff.2 fun h'' => by have := Nat.eq_of_beq_eq_true h''; omega
    rw [hpn] at h
    have hc : c < cdOf Rw p := Nat.blt_eq.mp h
    have hle : cdOf Rw p ≤ cdOf Rw r := by
      rcases Nat.lt_or_ge p r with h' | h'
      · exact (rec_lt hrow h' hr).le
      · rw [show r = p by omega]
    omega

theorem not_mem_of_gapK (hP : Nat.card ↥P1408 = 177408000) {Rw : ℕ → ℕ} {n k : ℕ}
    {gc : ℕ → ℕ} (hn : 0 < n) (hrow : ∀ r < n, recRow Rw n k gc r = true)
    (hgc : ∀ l < k, gc l < 30720) {c p : ℕ} (hc : c < 30720)
    (h : gapK (cdOf Rw) n c p = true) : elC c ∉ closure ((fun l => elC (gc l)) '' Set.Iio k) := by
  rw [(rec_facts hP hn hrow hgc).1]
  rintro ⟨r, hr, e⟩
  exact ne_of_gapK hrow h r hr (elC_inj (recRow_parts (hrow r hr)).1 hc e)

theorem mem_of_atK (hP : Nat.card ↥P1408 = 177408000) {Rw : ℕ → ℕ} {n k : ℕ}
    {gc : ℕ → ℕ} (hn : 0 < n) (hrow : ∀ r < n, recRow Rw n k gc r = true)
    (hgc : ∀ l < k, gc l < 30720) {c p : ℕ} (h : atK Rw n c p = true) :
    elC c ∈ closure ((fun l => elC (gc l)) '' Set.Iio k) := by
  unfold atK at h
  obtain ⟨a, b⟩ := mkA h
  rw [(rec_facts hP hn hrow hgc).1]
  exact ⟨p, Nat.blt_eq.mp a, by rw [Nat.eq_of_beq_eq_true b]⟩

theorem ncard_cntN (hP : Nat.card ↥P1408 = 177408000) {Rw : ℕ → ℕ} {n k : ℕ}
    {gc : ℕ → ℕ} (hn : 0 < n) (hrow : ∀ r < n, recRow Rw n k gc r = true)
    (hgc : ∀ l < k, gc l < 30720) {F : ℕ → Bool} {Q : Equiv.Perm (Fin 1408) → Prop}
    (hQ : ∀ r < n, F r = true ↔ Q (elC (cdOf Rw r))) :
    {x | x ∈ closure ((fun l => elC (gc l)) '' Set.Iio k) ∧ Q x}.ncard = cntN n F := by
  have hcd : ∀ r < n, cdOf Rw r < 30720 := fun r hr => (recRow_parts (hrow r hr)).1
  rw [cntN_eq', rec_ncard (rec_facts hP hn hrow hgc).1 _ hQ]
  intro r s hr hs e
  have ec := elC_inj (hcd r hr) (hcd s hs) e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd ec (rec_lt hrow hlt hs).ne
  · exact absurd ec (rec_lt hrow hlt hr).ne'

#kc_forall_chunks dsl_all (fun s => dSl s = true) 30 CFSG.KD.HN1408.ch441697.dsl 1

theorem dRows : ∀ r < 7680, recRow DR 7680 3 dGen r = true := by
  intro r hr
  have hs : r / 256 < 30 := by omega
  have h := dsl_all (r / 256) hs
  unfold dSl at h
  have h' := allN_spec h (r % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 256 (r / 256)) (r % 256) = r := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h'
  exact h'

theorem rRows : ∀ r < 256, recRow RR 256 7 rGen r = true := by
  intro r hr
  have h := r_ok
  unfold rAll at h
  exact (mkA (allN_spec h r hr)).1

theorem dGen_lt : ∀ l < 3, dGen l < 30720 := by
  intro l hl
  have h0 := dgens_ok
  unfold dGensK at h0
  have h := allN_spec h0 l hl
  simp only [strictB_x] at h
  exact Nat.blt_eq.mp (mkA h).1

theorem rGen_lt : ∀ l < 7, rGen l < 30720 := by
  intro l hl
  have h0 := rgens_ok
  unfold rGensK at h0
  have h := allN_spec h0 l hl
  simp only [strictB_x] at h
  exact Nat.blt_eq.mp (mkA h).1

abbrev dK : Subgroup (Equiv.Perm (Fin 1408)) := closure ((fun l => elC (dGen l)) '' Set.Iio 3)

abbrev rK : Subgroup (Equiv.Perm (Fin 1408)) := closure ((fun l => elC (rGen l)) '' Set.Iio 7)

theorem dk_facts (hP : Nat.card ↥P1408 = 177408000) :
    (∀ x, x ∈ dK ↔ ∃ r < 7680, elC (cdOf DR r) = x) ∧ Nat.card ↥dK = 7680 :=
  rec_facts hP (by norm_num) dRows dGen_lt

theorem rk_facts (hP : Nat.card ↥P1408 = 177408000) :
    (∀ x, x ∈ rK ↔ ∃ r < 256, elC (cdOf RR r) = x) ∧ Nat.card ↥rK = 256 :=
  rec_facts hP (by norm_num) rRows rGen_lt

theorem elC_rGen (hP : Nat.card ↥P1408 = 177408000) {l : ℕ} (hl : l < 7) :
    elC (rGen l) = elemW (nWords1.getD l []) := by
  have hH := headI_spec kH1
  have hlen : l < nWords1.length := by rw [hH.1]; exact hl
  have hw : nWords1.getD l [] ∈ nWords1 := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  have hrep := repC_word (hl1 _ hw)
  have hmem : elemW (nWords1.getD l []) ∈
      P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
    generalize nWords1.getD l [] = w at hw ⊢
    rw [nWords1, List.mem_map] at hw
    obtain ⟨s, -, rfl⟩ := hw
    exact le_cent (elemW_specWord_mem _ s)
  have h0 := rgens_ok
  unfold rGensK at h0
  have h := allN_spec h0 l hl
  simp only [strictB_x] at h
  rw [(hH.2.1 l hl).1] at h
  exact eq_of_eqB hP (elC_mem hP (rGen_lt l hl)) hmem (fun _ hx => ev_elC (rGen_lt l hl) hx)
    (fun _ hx => repC_pt hrep hx) (mkA h).2

theorem rK_eq (hP : Nat.card ↥P1408 = 177408000) :
    rK = HaradaModel.wordSubgroup nWords1 := by
  have hlen : nWords1.length = 7 := (headI_spec kH1).1
  unfold HaradaModel.wordSubgroup
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < nWords1.length := by rw [hlen]; exact hl
    refine subset_closure ⟨nWords1.getD l [], ?_, (elC_rGen hP hl).symm⟩
    rw [Set.mem_setOf_eq, List.getD_eq_getElem _ _ hl']
    exact List.getElem_mem hl'
  · rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hw
    have hl7 : l < 7 := by rw [← hlen]; exact hl
    have e := elC_rGen hP hl7
    rw [List.getD_eq_getElem _ _ hl] at e
    rw [← e]
    exact subset_closure ⟨l, hl7, rfl⟩

end CFSG.KD.HN1408.TabX

end
