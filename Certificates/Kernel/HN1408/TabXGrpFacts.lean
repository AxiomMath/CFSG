module

public import Certificates.Kernel.HN1408.TabXRecFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TwoFourAbstract
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeKAux

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TabX

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.BaseEq CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.Section3Model

noncomputable abbrev xK : Subgroup (Equiv.Perm (Fin 1408)) :=
  P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))

noncomputable abbrev uK (l : ℕ) : Equiv.Perm (Fin 1408) := elemW (classz.centGens.getD l [])

theorem uK_mem {l : ℕ} (hl : l < 2) : uK l ∈ xK := le_cent (gen_mem hl)

theorem dK_le (hP : Nat.card ↥P1408 = 177408000) : dK ≤ xK := by
  rw [closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact elC_mem hP (dGen_lt l hl)

theorem rK_le (hP : Nat.card ↥P1408 = 177408000) : rK ≤ xK := by
  rw [closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact elC_mem hP (rGen_lt l hl)

theorem ev_ev_ev {c h k x : ℕ} (hc : c < 30720) (hh : h < 30720) (hk : k < 30720)
    (hx : x < 1408) : ev c (ev h (ev k x)) = ((elC c * elC h * elC k) ⟨x, hx⟩).val := by
  rw [ev_elC hk hx, ev_ev hc hh (Fin.isLt _)]
  rfl

theorem cd_lt_D {r : ℕ} (hr : r < 7680) : cdOf DR r < 30720 := (recRow_parts (dRows r hr)).1

theorem cd_lt_R {r : ℕ} (hr : r < 256) : cdOf RR r < 30720 := (recRow_parts (rRows r hr)).1

theorem mem_dK (hP : Nat.card ↥P1408 = 177408000) {r : ℕ} (hr : r < 7680) :
    elC (cdOf DR r) ∈ dK := ((dk_facts hP).1 _).2 ⟨r, hr, rfl⟩

theorem mem_rK (hP : Nat.card ↥P1408 = 177408000) {r : ℕ} (hr : r < 256) :
    elC (cdOf RR r) ∈ rK := ((rk_facts hP).1 _).2 ⟨r, hr, rfl⟩

theorem not_mem_dK (hP : Nat.card ↥P1408 = 177408000) {c p : ℕ} (hc : c < 30720)
    (h : gapK (cdOf DR) 7680 c p = true) : elC c ∉ dK :=
  not_mem_of_gapK hP (by norm_num) dRows dGen_lt hc h

theorem not_mem_rK (hP : Nat.card ↥P1408 = 177408000) {c p : ℕ} (hc : c < 30720)
    (h : gapK (cdOf RR) 256 c p = true) : elC c ∉ rK :=
  not_mem_of_gapK hP (by norm_num) rRows rGen_lt hc h

theorem conj_mem_closure {G : Type} [Group G] {s : Set G} {u : G}
    (h : ∀ g ∈ s, u * g * u⁻¹ ∈ closure s) : ∀ d ∈ closure s, u * d * u⁻¹ ∈ closure s := by
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul a b _ _ ha hb =>
    have e : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem dgens_parts (hP : Nat.card ↥P1408 = 177408000) {m : ℕ} (hm : m < 3) :
    ∃ x y, x < 30720 ∧ y < 30720 ∧ elC (dGen m) = elC x * elC y * (elC x)⁻¹ * (elC y)⁻¹ := by
  have h0 := dgens_ok
  unfold dGensK at h0
  have h := allN_spec h0 m hm
  simp only [strictB_x] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, e⟩ := mkA h
  have hd := Nat.blt_eq.mp a
  have hx := Nat.blt_eq.mp b
  have hy := Nat.blt_eq.mp c
  refine ⟨_, _, hx, hy, ?_⟩
  have e' := eq_of_eqB hP (mul_mem (mul_mem (elC_mem hP hd) (elC_mem hP hy)) (elC_mem hP hx))
    (mul_mem (elC_mem hP hx) (elC_mem hP hy)) (fun _ hp => ev_ev_ev hd hy hx hp)
    (fun _ hp => ev_ev hx hy hp) e
  rw [← e']
  group

theorem norm_parts (hP : Nat.card ↥P1408 = 177408000) {l m : ℕ} (hl : l < 2) (hm : m < 3) :
    uK l * elC (dGen m) * (uK l)⁻¹ ∈ dK ∧ (uK l)⁻¹ * elC (dGen m) * (uK l)⁻¹⁻¹ ∈ dK := by
  have h0 := norm_ok
  unfold normK at h0
  have h1 := allN_spec h0 l hl
  simp only [strictB_x] at h1
  have h := allN_spec h1 m hm
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨e1, e2⟩ := mkA h
  have ha := Nat.blt_eq.mp a
  have hb := Nat.blt_eq.mp b
  have hU := repC_G hl
  have hd := dGen_lt m hm
  have hu := uK_mem hl
  have f1 := eq_of_eqB hP (mul_mem hu (elC_mem hP hd)) (mul_mem (elC_mem hP (cd_lt_D ha)) hu)
    (fun x hx => by rw [ev_elC hd hx, repC_pt hU (Fin.isLt _)]; rfl)
    (fun x hx => by rw [repC_pt hU hx, ev_elC (cd_lt_D ha) (Fin.isLt _)]; rfl) e1
  have f2 := eq_of_eqB hP (mul_mem (elC_mem hP hd) hu) (mul_mem hu (elC_mem hP (cd_lt_D hb)))
    (fun x hx => by rw [repC_pt hU hx, ev_elC hd (Fin.isLt _)]; rfl)
    (fun x hx => by rw [ev_elC (cd_lt_D hb) hx, repC_pt hU (Fin.isLt _)]; rfl) e2
  constructor
  · rw [f1, mul_inv_cancel_right]
    exact mem_dK hP ha
  · rw [inv_inv, mul_assoc, f2, inv_mul_cancel_left]
    exact mem_dK hP hb

theorem conj_mem_dK (hP : Nat.card ↥P1408 = 177408000) :
    ∀ x ∈ xK, ∀ d ∈ dK, x * d * x⁻¹ ∈ dK := by
  let S : Subgroup (Equiv.Perm (Fin 1408)) :=
    { carrier := {x | (∀ d ∈ dK, x * d * x⁻¹ ∈ dK) ∧ ∀ d ∈ dK, x⁻¹ * d * x⁻¹⁻¹ ∈ dK}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨fun d hd => ?_, fun d hd => ?_⟩
        · have e : a * b * d * (a * b)⁻¹ = a * (b * d * b⁻¹) * a⁻¹ := by group
          rw [e]
          exact ha.1 _ (hb.1 d hd)
        · have e : (a * b)⁻¹ * d * (a * b)⁻¹⁻¹ = b⁻¹ * (a⁻¹ * d * a⁻¹⁻¹) * b⁻¹⁻¹ := by group
          rw [e]
          exact hb.2 _ (ha.2 d hd)
      one_mem' := ⟨fun d hd => by simpa using hd, fun d hd => by simpa using hd⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by simpa only [inv_inv] using ha.1⟩ }
  have hS : czC ≤ S := by
    rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨l, hl, rfl⟩ : ∃ l < 2, classz.centGens.getD l [] = w := by
      have hw' : w ∈ classz.centGens := hw
      simp only [classz, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    refine ⟨conj_mem_closure ?_, conj_mem_closure ?_⟩
    · rintro _ ⟨m, hm, rfl⟩
      exact (norm_parts hP hl hm).1
    · rintro _ ⟨m, hm, rfl⟩
      exact (norm_parts hP hl hm).2
  intro x hx d hd
  have hx' : x ∈ czC := by
    rw [(czT_eq hP).1]
    exact hx
  exact (hS hx').1 d hd

theorem quot_parts (hP : Nat.card ↥P1408 = 177408000) :
    uK 0 * uK 0 ∈ dK ∧ uK 1 * uK 1 ∈ dK ∧ uK 0 ∉ dK ∧ uK 1 ∉ dK ∧ uK 0 * (uK 1)⁻¹ ∉ dK := by
  have h := quot_ok
  unfold quotK at h
  simp only [strictB_x] at h
  generalize hN : nm = N at h
  generalize hG : G = Gt at h
  obtain ⟨a1, h⟩ := mkA h
  obtain ⟨a2, h⟩ := mkA h
  obtain ⟨a3, h⟩ := mkA h
  obtain ⟨e1, h⟩ := mkA h
  obtain ⟨e2, h⟩ := mkA h
  obtain ⟨b1, h⟩ := mkA h
  obtain ⟨b2, h⟩ := mkA h
  obtain ⟨s1, h⟩ := mkA h
  obtain ⟨s2, h⟩ := mkA h
  obtain ⟨v1, h⟩ := mkA h
  obtain ⟨g1, h⟩ := mkA h
  obtain ⟨g2, g3⟩ := mkA h
  subst hN hG
  have h1 := Nat.blt_eq.mp a1
  have h2 := Nat.blt_eq.mp a2
  have h3 := Nat.blt_eq.mp a3
  have hb1 := Nat.blt_eq.mp b1
  have hb2 := Nat.blt_eq.mp b2
  have r0 := repC_G (l := 0) (by norm_num)
  have r1 := repC_G (l := 1) (by norm_num)
  have u0 := uK_mem (l := 0) (by norm_num)
  have u1 := uK_mem (l := 1) (by norm_num)
  have f1 : elC (nm 21) = uK 0 := eq_of_eqB hP (elC_mem hP h1) u0
    (fun _ hx => ev_elC h1 hx) (fun _ hx => repC_pt r0 hx) e1
  have f2 : elC (nm 22) = uK 1 := eq_of_eqB hP (elC_mem hP h2) u1
    (fun _ hx => ev_elC h2 hx) (fun _ hx => repC_pt r1 hx) e2
  have f3 : elC (cdOf DR (nm 23)) = uK 0 * uK 0 :=
    eq_of_eqB hP (elC_mem hP (cd_lt_D hb1)) (mul_mem u0 u0)
      (fun _ hx => ev_elC (cd_lt_D hb1) hx)
      (fun x hx => by rw [repC_pt r0 hx, repC_pt r0 (Fin.isLt _)]; rfl) s1
  have f4 : elC (cdOf DR (nm 24)) = uK 1 * uK 1 :=
    eq_of_eqB hP (elC_mem hP (cd_lt_D hb2)) (mul_mem u1 u1)
      (fun _ hx => ev_elC (cd_lt_D hb2) hx)
      (fun x hx => by rw [repC_pt r1 hx, repC_pt r1 (Fin.isLt _)]; rfl) s2
  have f5 : elC (nm 25) * uK 1 = uK 0 :=
    eq_of_eqB hP (mul_mem (elC_mem hP h3) u1) u0
      (fun x hx => by rw [repC_pt r1 hx, ev_elC h3 (Fin.isLt _)]; rfl)
      (fun _ hx => repC_pt r0 hx) v1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← f3]
    exact mem_dK hP hb1
  · rw [← f4]
    exact mem_dK hP hb2
  · rw [← f1]
    exact not_mem_dK hP h1 g1
  · rw [← f2]
    exact not_mem_dK hP h2 g2
  · rw [← f5, mul_inv_cancel_right]
    exact not_mem_dK hP h3 g3

theorem dK_eq (hP : Nat.card ↥P1408 = 177408000) : derivedOf xK = dK := by
  have hle := dK_le hP
  obtain ⟨hs1, hs2, hn1, hn2, hn12⟩ := quot_parts hP
  have hcard : Nat.card ↥xK = 4 * Nat.card ↥dK := by
    have e : xK = czC := (czT_eq hP).1.symm
    rw [(dk_facts hP).2, e, (czT_eq hP).2]
  apply le_antisymm
  · exact derivedOf_le_of_quotShape hle (quotShape_elem2_two hle (conj_mem_dK hP) hcard
      (uK_mem (by norm_num)) (uK_mem (by norm_num)) hs1 hs2 hn1 hn2 hn12)
  · rw [closure_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨x, y, hx, hy, e⟩ := dgens_parts hP hm
    beta_reduce
    rw [e]
    exact commutator_mem_derivedOf (elC_mem hP hx) (elC_mem hP hy)

theorem named_facts (hP : Nat.card ↥P1408 = 177408000) :
    nm 62 < 30720 ∧ elC (nm 62) = elemB ∧ elemB ∈ rK ∧ nm 63 < 30720 ∧
      elC (nm 63) = t0P 817 * t1P 0 ∧ elC (nm 63) ∉ rK ∧
      ∃ m₁ ∈ dK, ∃ m₂ ∈ dK, m₁ * elC (nm 63) = elC (nm 63) * m₁ ∧
        m₂ * elC (nm 63) = elC (nm 63) * m₂ ∧ m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∉ rK := by
  have h := named_ok
  unfold namedK at h
  simp only [strictB_x] at h
  generalize hN : nm = N at h
  generalize hW : WK wordB = Wb at h
  obtain ⟨a1, h⟩ := mkA h
  obtain ⟨a2, h⟩ := mkA h
  obtain ⟨a3, h⟩ := mkA h
  obtain ⟨eb, h⟩ := mkA h
  obtain ⟨at0, h⟩ := mkA h
  obtain ⟨g1, h⟩ := mkA h
  obtain ⟨b1, h⟩ := mkA h
  obtain ⟨b2, h⟩ := mkA h
  obtain ⟨k1, h⟩ := mkA h
  obtain ⟨k2, h⟩ := mkA h
  obtain ⟨ec, g2⟩ := mkA h
  subst hN hW
  have h0 := Nat.blt_eq.mp a1
  have h1 := Nat.eq_of_beq_eq_true a2
  have he := Nat.blt_eq.mp a3
  have hb1 := Nat.blt_eq.mp b1
  have hb2 := Nat.blt_eq.mp b2
  have hB : RepC (WK wordB) elemB := repC_word (by decide)
  have hBm : elemB ∈ xK := by
    obtain ⟨hq, hq', he'⟩ := CzInv.named_eq hP (c := 3) (by norm_num)
    have hb : CzInv.namedA 3 = elemB := by simp [CzInv.namedA, CzInv.namedE]
    rw [hb] at he'
    rw [← he']
    exact CzInv.mem_cz hP hq hq'
  have fb : elC (nm 62) = elemB := eq_of_eqB hP (elC_mem hP h0) hBm
    (fun _ hx => ev_elC h0 hx) (fun _ hx => repC_pt hB hx) eb
  have h63 : nm 63 < 30720 := by
    rw [h1]
    norm_num
  have fc : elC (nm 63) = t0P 817 * t1P 0 := by
    have e1 : Nat.div 19608 24 = 817 := by norm_num
    have e2 : Nat.mod 19608 24 = 0 := by norm_num
    have v : ∀ x (hx : x < 1408),
        (elC (nm 63) ⟨x, hx⟩).val = ((t0P 817 * t1P 0) ⟨x, hx⟩).val := by
      intro x hx
      rw [← ev_elC h63 hx, h1, ev.eq_1, e1, e2]
      exact ev_eq (by norm_num) (by norm_num) hx
    exact eq_of_base hP (elC_mem hP h63) (CzInv.mem_cz hP (by norm_num) (by norm_num))
      (Fin.ext (v 0 (by norm_num))) (Fin.ext (v 1 (by norm_num)))
  have hm1 := cd_lt_D hb1
  have hm2 := cd_lt_D hb2
  have c1 := (commC_iff hP hm1 h63).1 k1
  have c2 := (commC_iff hP hm2 h63).1 k2
  have fe := eq_of_eqB hP (mul_mem (mul_mem (elC_mem hP he) (elC_mem hP hm2)) (elC_mem hP hm1))
    (mul_mem (elC_mem hP hm1) (elC_mem hP hm2)) (fun _ hx => ev_ev_ev he hm2 hm1 hx)
    (fun _ hx => ev_ev hm1 hm2 hx) ec
  refine ⟨h0, fb, ?_, h63, fc, not_mem_rK hP h63 g1, _, mem_dK hP hb1, _, mem_dK hP hb2, c1, c2,
    ?_⟩
  · rw [← fb]
    exact mem_of_atK hP (by norm_num) rRows rGen_lt at0
  · have e : elC (cdOf DR (nm 38)) * elC (cdOf DR (nm 39)) * (elC (cdOf DR (nm 38)))⁻¹ *
        (elC (cdOf DR (nm 39)))⁻¹ = elC (nm 40) := by
      rw [← fe]
      group
    rw [e]
    exact not_mem_rK hP he g2

theorem sig_facts (hP : Nat.card ↥P1408 = 177408000) :
    nm 60 < 30720 ∧ elC (nm 60) ∈ xK ∧ orderOf (elC (nm 60)) = 3 ∧ elC (nm 61) ∈ xK ∧
      elC (nm 61) * elC (nm 60) * (elC (nm 61))⁻¹ = (elC (nm 60))⁻¹ ∧
      elemB * elC (nm 60) = elC (nm 60) * elemB ∧
      ∀ k < 8, zc k < 30720 → elC (zc k) * elC (nm 60) = elC (nm 60) * elC (zc k) := by
  have h := sig_ok
  unfold sigK at h
  simp only [strictB_x] at h
  generalize hN : nm = N at h
  obtain ⟨a1, h⟩ := mkA h
  obtain ⟨a2, h⟩ := mkA h
  obtain ⟨n0, h⟩ := mkA h
  obtain ⟨e3, h⟩ := mkA h
  obtain ⟨et, h⟩ := mkA h
  obtain ⟨cb, h⟩ := mkA h
  obtain ⟨-, hz⟩ := mkA h
  subst hN
  have hs := Nat.blt_eq.mp a1
  have ht := Nat.blt_eq.mp a2
  obtain ⟨h62, fb, -⟩ := named_facts hP
  have sm := elC_mem hP hs
  have tm := elC_mem hP ht
  have hne : elC (nm 60) ≠ 1 := by
    intro e
    rw [← elC_zero] at e
    have e' := elC_inj hs (by norm_num) e
    rw [e', Nat.beq_refl] at n0
    exact Bool.false_ne_true n0
  have h3 : elC (nm 60) * elC (nm 60) * elC (nm 60) = 1 :=
    eq_of_eqB hP (mul_mem (mul_mem sm sm) sm) (one_mem _) (fun _ hx => ev_ev_ev hs hs hs hx)
      (fun _ _ => rfl) e3
  have ht3 : elC (nm 60) * elC (nm 61) * elC (nm 60) = elC (nm 61) :=
    eq_of_eqB hP (mul_mem (mul_mem sm tm) sm) tm (fun _ hx => ev_ev_ev hs ht hs hx)
      (fun _ hx => ev_elC ht hx) et
  refine ⟨hs, sm, ?_, tm, ?_, ?_, fun k hk hzk => ?_⟩
  · refine orderOf_eq_prime ?_ hne
    rw [pow_three, ← mul_assoc]
    exact h3
  · have e : elC (nm 61) * elC (nm 60) * (elC (nm 61))⁻¹ =
        (elC (nm 60))⁻¹ * (elC (nm 60) * elC (nm 61) * elC (nm 60)) * (elC (nm 61))⁻¹ := by
      group
    rw [e, ht3]
    group
  · rw [← fb]
    exact (commC_iff hP h62 hs).1 cb
  · exact (commC_iff hP hzk hs).1 (allN_spec hz k hk)

theorem card_eq_ncard_of {G : Type} [Group G] {H S : Subgroup G} {Q : G → Prop}
    (h : ∀ x, x ∈ H ↔ x ∈ S ∧ Q x) : Nat.card ↥H = {x | x ∈ S ∧ Q x}.ncard := by
  have hc : Nat.card ↥H = (H : Set G).ncard := Nat.card_coe_set_eq _
  rw [hc]
  congr 1
  ext x
  exact h x

theorem inD_iff (hP : Nat.card ↥P1408 = 177408000) {r : ℕ} (hr : r < 256) :
    inD r = true ↔ elC (cdOf RR r) ∈ dK := by
  have h0 := r_ok
  unfold rAll at h0
  have hp := (mkA (allN_spec h0 r hr)).2
  unfold posK at hp
  unfold inD
  simp only [strictB_x] at hp ⊢
  constructor
  · intro h
    exact mem_of_atK hP (by norm_num) dRows dGen_lt h
  · intro hm
    cases e : atK DR 7680 (fd (RR r) 0) (fd (RR r) 11)
    · rw [e] at hp
      exact absurd hm (not_mem_dK hP (cd_lt_R hr) hp)
    · rfl

theorem card_cntR (hP : Nat.card ↥P1408 = 177408000) {H : Subgroup (Equiv.Perm (Fin 1408))}
    {F : ℕ → Bool} {Q : Equiv.Perm (Fin 1408) → Prop} (hH : ∀ x, x ∈ H ↔ x ∈ rK ∧ Q x)
    (hQ : ∀ r < 256, F r = true ↔ Q (elC (cdOf RR r))) : Nat.card ↥H = cntN 256 F := by
  rw [card_eq_ncard_of hH]
  exact ncard_cntN hP (by norm_num) rRows rGen_lt hQ

theorem card_cntD (hP : Nat.card ↥P1408 = 177408000) {H : Subgroup (Equiv.Perm (Fin 1408))}
    {F : ℕ → Bool} {Q : Equiv.Perm (Fin 1408) → Prop} (hH : ∀ x, x ∈ H ↔ x ∈ dK ∧ Q x)
    (hQ : ∀ r < 7680, F r = true ↔ Q (elC (cdOf DR r))) : Nat.card ↥H = cntN 7680 F := by
  rw [card_eq_ncard_of hH]
  exact ncard_cntN hP (by norm_num) dRows dGen_lt hQ

theorem mem_xc_iff {S : Subgroup (Equiv.Perm (Fin 1408))} (hS : S ≤ xK)
    {c x : Equiv.Perm (Fin 1408)} :
    x ∈ xK ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408))) ⊓ S ↔ x ∈ S ∧ x * c = c * x := by
  rw [mem_inf, mem_inf, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hS h.1, h.2⟩, h.1⟩⟩

theorem mem_xcRD_iff (hP : Nat.card ↥P1408 = 177408000) {c x : Equiv.Perm (Fin 1408)} :
    x ∈ xK ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408))) ⊓ rK ⊓ dK ↔
      x ∈ rK ∧ (x ∈ dK ∧ x * c = c * x) := by
  rw [mem_inf, mem_xc_iff (rK_le hP)]
  exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

theorem cnt_eq (i : ℕ) (h : cntOK i = true) : cntK i = cntV i := Nat.eq_of_beq_eq_true h

theorem commQ (hP : Nat.card ↥P1408 = 177408000) {c : ℕ} (hc : c < 30720) {r : ℕ} (hr : r < 256) :
    commC (cdOf RR r) c = true ↔ elC (cdOf RR r) * elC c = elC c * elC (cdOf RR r) :=
  commC_iff hP (cd_lt_R hr) hc

theorem commQD (hP : Nat.card ↥P1408 = 177408000) {c : ℕ} (hc : c < 30720) {r : ℕ}
    (hr : r < 7680) :
    commC (cdOf DR r) c = true ↔ elC (cdOf DR r) * elC c = elC c * elC (cdOf DR r) :=
  commC_iff hP (cd_lt_D hr) hc

theorem card_cent3 (hP : Nat.card ↥P1408 = 177408000) {h : ℕ} (hh : h < 30720) :
    Nat.card ↥(xK ⊓ centralizer ({elC h} : Set (Equiv.Perm (Fin 1408))) ⊓ rK) =
        cntR (fun _ c => commC c h) ∧
      Nat.card ↥(xK ⊓ centralizer ({elC h} : Set (Equiv.Perm (Fin 1408))) ⊓ rK ⊓ dK) =
        cntR (fun r c => bAnd(inD r, commC c h)) ∧
      Nat.card ↥(xK ⊓ centralizer ({elC h} : Set (Equiv.Perm (Fin 1408))) ⊓ dK) =
        cntD (fun c => commC c h) := by
  refine ⟨card_cntR hP (fun _ => mem_xc_iff (rK_le hP)) fun r hr => commQ hP hh hr,
    card_cntR hP (fun _ => mem_xcRD_iff hP) fun r hr => ?_,
    card_cntD hP (fun _ => mem_xc_iff (dK_le hP)) fun r hr => commQD hP hh hr⟩
  beta_reduce
  rw [bAnd_iff, inD_iff hP hr, commQ hP hh hr]

theorem card_c0 (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(xK ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) ⊓ rK) = 128 ∧
      Nat.card ↥(xK ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) ⊓ rK ⊓ dK) = 64 ∧
      Nat.card ↥(xK ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) ⊓ dK) = 192 := by
  obtain ⟨h62, fb, -⟩ := named_facts hP
  obtain ⟨a, b, c⟩ := card_cent3 hP h62
  rw [fb] at a b c
  exact ⟨a.trans (cnt_eq 0 ch441697.cnt0), b.trans (cnt_eq 1 ch441697.cnt1),
    c.trans (cnt_eq 2 ch441697.cnt2)⟩

theorem card_c1 (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(xK ⊓ centralizer ({elC (nm 63)} : Set (Equiv.Perm (Fin 1408))) ⊓ rK) = 32 ∧
      Nat.card ↥(xK ⊓ centralizer ({elC (nm 63)} : Set (Equiv.Perm (Fin 1408))) ⊓ rK ⊓ dK) =
        16 ∧
      Nat.card ↥(xK ⊓ centralizer ({elC (nm 63)} : Set (Equiv.Perm (Fin 1408))) ⊓ dK) = 96 := by
  obtain ⟨-, -, -, h63, -⟩ := named_facts hP
  obtain ⟨a, b, c⟩ := card_cent3 hP h63
  exact ⟨a.trans (cnt_eq 3 ch441697.cnt3), b.trans (cnt_eq 4 ch441697.cnt4),
    c.trans (cnt_eq 5 ch441697.cnt5)⟩

theorem card_cent_c1' (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(xK ⊓ centralizer ({elC (nm 63)} : Set (Equiv.Perm (Fin 1408)))) = 384 := by
  obtain ⟨-, -, -, -, fc, -⟩ := named_facts hP
  rw [fc]
  exact card_cent_of_stabK hP (repC_pc (t0P_spec (by norm_num)).2 (t1P_spec (by norm_num)).2)
    (CzInv.mem_cz hP (by norm_num) (by norm_num)) stab1_ok

theorem sq_c1R (hP : Nat.card ↥P1408 = 177408000) :
    ∀ x ∈ xK ⊓ centralizer ({elC (nm 63)} : Set (Equiv.Perm (Fin 1408))) ⊓ rK, x * x = 1 := by
  obtain ⟨-, -, -, h63, -⟩ := named_facts hP
  intro x hx
  obtain ⟨hr, hc⟩ := (mem_xc_iff (rK_le hP)).1 hx
  obtain ⟨r, hr', rfl⟩ := ((rk_facts hP).1 _).1 hr
  have h0 := sq_ok
  unfold sqK at h0
  have h := allN_spec h0 r hr'
  simp only [strictB_x] at h
  have hcc : commC (cdOf RR r) (nm 63) = true := (commQ hP h63 hr').2 hc
  rw [hcc] at h
  exact eq_of_eqB hP (mul_mem (elC_mem hP (cd_lt_R hr')) (elC_mem hP (cd_lt_R hr'))) (one_mem _)
    (fun _ hx => ev_ev (cd_lt_R hr') (cd_lt_R hr') hx) (fun _ _ => rfl) h

theorem card_DR (hP : Nat.card ↥P1408 = 177408000) : Nat.card ↥(dK ⊓ rK) = 128 := by
  have h := card_cntR hP (H := dK ⊓ rK) (Q := fun x => x ∈ dK) (F := fun r => inD r)
    (fun x => by rw [mem_inf]; exact And.comm) (fun r hr => inD_iff hP hr)
  exact h.trans (cnt_eq 6 ch441697.cnt6)

theorem card_DRs (hP : Nat.card ↥P1408 = 177408000) : Nat.card ↥(dK ⊔ rK) = 15360 := by
  have hn : rK ≤ normalizer (dK : Set (Equiv.Perm (Fin 1408))) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    have hx := rK_le hP hg
    refine ⟨fun hh => conj_mem_dK hP g hx h hh, fun hh => ?_⟩
    have e := conj_mem_dK hP g⁻¹ (inv_mem hx) _ hh
    have e' : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e'] at e
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hn
  rw [inf_comm, card_DR hP, (rk_facts hP).2, (dk_facts hP).2, sup_comm] at h
  omega

theorem card_sig (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(rK ⊓ centralizer ({elC (nm 60)} : Set (Equiv.Perm (Fin 1408)))) = 16 ∧
      Nat.card ↥(dK ⊓ rK ⊓ centralizer ({elC (nm 60)} : Set (Equiv.Perm (Fin 1408)))) = 8 := by
  have hs := (sig_facts hP).1
  have a := card_cntR hP (H := rK ⊓ centralizer ({elC (nm 60)} : Set (Equiv.Perm (Fin 1408))))
    (F := fun r => commC (cdOf RR r) (nm 60)) (Q := fun x => x * elC (nm 60) = elC (nm 60) * x)
    (fun x => by rw [mem_inf, mem_centralizer_singleton_iff]) (fun r hr => commQ hP hs hr)
  have b := card_cntR hP
    (H := dK ⊓ rK ⊓ centralizer ({elC (nm 60)} : Set (Equiv.Perm (Fin 1408))))
    (F := fun r => bAnd(inD r, commC (cdOf RR r) (nm 60)))
    (Q := fun x => x ∈ dK ∧ x * elC (nm 60) = elC (nm 60) * x)
    (fun x => by
      rw [mem_inf, mem_inf, mem_centralizer_singleton_iff]
      exact ⟨fun h => ⟨h.1.2, h.1.1, h.2⟩, fun h => ⟨⟨h.2.1, h.1⟩, h.2.2⟩⟩)
    (fun r hr => by rw [bAnd_iff, inD_iff hP hr, commQ hP hs hr])
  exact ⟨a.trans (cnt_eq 8 ch441697.cnt8), b.trans (cnt_eq 9 ch441697.cnt9)⟩

private theorem allBlk_of' {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_of' (fun l hl => h l (Nat.lt_succ_of_lt hl))]

private theorem rec_blocks_of' {f : Nat → Bool} : ∀ {q : Nat},
    (∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true
  | 0, _ => rfl
  | q + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true
    rw [h q (Nat.lt_succ_self q), rec_blocks_of' (fun h' hh => h h' (Nat.lt_succ_of_lt hh))]

private theorem allN_of_forall' {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) :
    allN n f = true := by
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true
  have hd := Nat.div_add_mod n 64
  rw [allBlk_of' (fun l hl => h _ (by rw [e6, e64, Nat.add_eq]; rw [er] at hl; omega)),
    rec_blocks_of' (fun q hq => allBlk_of' (fun l hl => h _ (by
      have hl' : l < 64 := hl
      rw [e6, Nat.add_eq]; rw [e64] at hq; omega)))]

private theorem allN_iffT {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  ⟨allN_spec, allN_of_forall'⟩

theorem eq_false_of_bIf {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem comm_of_gens {s : Set (Equiv.Perm (Fin 1408))} {x : Equiv.Perm (Fin 1408)}
    (h : ∀ g ∈ s, g * x = x * g) : ∀ d ∈ closure s, d * x = x * d := by
  have hle : closure s ≤ centralizer ({x} : Set (Equiv.Perm (Fin 1408))) := by
    rw [closure_le]
    intro g hg
    exact mem_centralizer_singleton_iff.2 (h g hg)
  intro d hd
  exact mem_centralizer_singleton_iff.1 (hle hd)

theorem mem_zD_iff {x : Equiv.Perm (Fin 1408)} :
    x ∈ centerOf dK ↔ x ∈ dK ∧ ∀ m < 3, x * elC (dGen m) = elC (dGen m) * x := by
  unfold centerOf
  rw [mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, fun m hm => (hc _ (subset_closure ⟨m, hm, rfl⟩)).symm⟩
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun d hd => comm_of_gens (fun g hg => ?_) d hd⟩
    obtain ⟨m, hm, rfl⟩ := hg
    exact (hc m hm).symm

theorem card_zD (hP : Nat.card ↥P1408 = 177408000) : Nat.card ↥(centerOf dK) = 8 := by
  have a := card_cntD hP (H := centerOf dK)
    (F := fun r => allN 3 fun m => commC (cdOf DR r) (dGen m))
    (Q := fun x => ∀ m < 3, x * elC (dGen m) = elC (dGen m) * x) (fun _ => mem_zD_iff)
    (fun r hr => by
      rw [allN_iffT]
      exact forall₂_congr fun m hm => commC_iff hP (cd_lt_D hr) (dGen_lt m hm))
  exact a.trans (cnt_eq 7 ch441697.cnt7)

theorem z_parts :
    (∀ k < 4, fd (ZG 0) k < 256 ∧ inD (fd (ZG 0) k) = true) ∧
      (∀ k < 8, nm (Nat.add 42 k) < 7680 ∧ (k < 7 → nm (Nat.add 42 k) < nm (Nat.add 43 k)) ∧
        (∀ m < 3, commC (zc k) (dGen m) = true) ∧ atK RR 256 (zc k) (nm (Nat.add 50 k)) = true ∧
        zc k ≠ nm 62) ∧
      nm 58 < 8 ∧ nm 59 < 8 ∧
      eqB (fun x => ev (zc (nm 58)) (ev (zc (nm 58)) x)) (fun x => x) = false ∧
      eqB (fun x => ev (zc (nm 58)) (ev (zc (nm 58)) (ev (zc (nm 58)) (ev (zc (nm 58)) x))))
        (fun x => x) = true ∧
      zc (nm 59) ≠ 0 ∧ eqB (fun x => ev (zc (nm 59)) (ev (zc (nm 59)) x)) (fun x => x) = true ∧
      eqB (fun x => ev (zc (nm 59)) x) (fun x => ev (zc (nm 58)) (ev (zc (nm 58)) x)) = false := by
  have h := z_ok
  unfold zK at h
  simp only [strictB_x] at h
  generalize hN : nm = N at h
  generalize hZ : ZG = Zg at h
  obtain ⟨hA, h⟩ := mkA h
  obtain ⟨hB, h⟩ := mkA h
  obtain ⟨b58, h⟩ := mkA h
  obtain ⟨b59, h⟩ := mkA h
  obtain ⟨n4, h⟩ := mkA h
  obtain ⟨p4, h⟩ := mkA h
  obtain ⟨n2, h⟩ := mkA h
  obtain ⟨p2, q2⟩ := mkA h
  subst hN hZ
  refine ⟨fun k hk => ?_, fun k hk => ?_, Nat.blt_eq.mp b58, Nat.blt_eq.mp b59,
    eq_false_of_bIf n4, p4, fun e => ?_, p2, eq_false_of_bIf q2⟩
  · obtain ⟨a, b⟩ := mkA (allN_spec hA k hk)
    exact ⟨Nat.blt_eq.mp a, b⟩
  · have h1 := allN_spec hB k hk
    obtain ⟨a, h1⟩ := mkA h1
    obtain ⟨b, h1⟩ := mkA h1
    obtain ⟨c, h1⟩ := mkA h1
    obtain ⟨d, e⟩ := mkA h1
    refine ⟨Nat.blt_eq.mp a, fun hk7 => ?_, allN_spec c, d, fun he => ?_⟩
    · rw [Nat.blt_eq.mpr hk7] at b
      exact Nat.blt_eq.mp b
    · have e' := eq_false_of_bIf e
      rw [he, Nat.beq_refl] at e'
      exact Bool.false_ne_true e'.symm
  · have e' := eq_false_of_bIf (b := Nat.beq (zc (nm 59)) 0) n2
    rw [e, Nat.beq_refl] at e'
    exact Bool.false_ne_true e'.symm

theorem zc_lt {k : ℕ} (hk : k < 8) : zc k < 30720 := cd_lt_D (z_parts.2.1 k hk).1

theorem zD_list (hP : Nat.card ↥P1408 = 177408000) :
    ∀ x, x ∈ centerOf dK ↔ ∃ k < 8, elC (zc k) = x := by
  classical
  have hB := z_parts.2.1
  have hmem : ∀ k < 8, elC (zc k) ∈ centerOf dK := fun k hk => mem_zD_iff.2
    ⟨mem_dK hP (hB k hk).1, fun m hm =>
      (commC_iff hP (zc_lt hk) (dGen_lt m hm)).1 ((hB k hk).2.2.1 m hm)⟩
  have hpos : ∀ k k', k < k' → k' < 8 → nm (Nat.add 42 k) < nm (Nat.add 42 k') := by
    intro k k' h h'
    induction k' with
    | zero => exact absurd h (Nat.not_lt_zero _)
    | succ k' ih =>
      have e := (hB k' (by omega)).2.1 (by omega)
      have e' : Nat.add 43 k' = Nat.add 42 (k' + 1) := by
        simp only [Nat.add_eq]
        omega
      rw [e'] at e
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h'' | h''
      · exact (ih h'' (by omega)).trans e
      · rw [h'']
        exact e
  have hinj : ∀ k k', k < 8 → k' < 8 → elC (zc k) = elC (zc k') → k = k' := by
    intro k k' hk hk' e
    have ec := elC_inj (zc_lt hk) (zc_lt hk') e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd ec (rec_lt dRows (hpos k k' h hk') (hB k' hk').1).ne
    · exact absurd ec (rec_lt dRows (hpos k' k h hk) (hB k hk).1).ne'
  let S : Finset (Equiv.Perm (Fin 1408)) := (Finset.range 8).image fun k => elC (zc k)
  have hSc : S.card = 8 := by
    rw [Finset.card_image_of_injOn (fun k hk k' hk' e => hinj k k' (Finset.mem_range.1 hk)
      (Finset.mem_range.1 hk') e), Finset.card_range]
  have hS : (S : Set (Equiv.Perm (Fin 1408))) = (centerOf dK : Set (Equiv.Perm (Fin 1408))) := by
    apply Set.eq_of_subset_of_ncard_le
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      exact hmem k (Finset.mem_range.1 hk)
    · rw [Set.ncard_coe_finset, hSc, ← Nat.card_coe_set_eq]
      exact (card_zD hP).le
    · exact Set.toFinite _
  intro x
  rw [← SetLike.mem_coe, ← hS, Finset.mem_coe, Finset.mem_image]
  simp only [Finset.mem_range]

theorem zD_le_R (hP : Nat.card ↥P1408 = 177408000) : centerOf dK ≤ rK := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := (zD_list hP x).1 hx
  exact mem_of_atK hP (by norm_num) rRows rGen_lt (z_parts.2.1 k hk).2.2.2.1

theorem zD_eq (hP : Nat.card ↥P1408 = 177408000) : centerOf dK = centerOf (dK ⊓ rK) := by
  classical
  have hA := z_parts.1
  let g : ℕ → Equiv.Perm (Fin 1408) := fun k => elC (cdOf RR (fd (ZG 0) k))
  have hgD : ∀ k < 4, g k ∈ dK := fun k hk => (inD_iff hP (hA k hk).1).1 (hA k hk).2
  have hgR : ∀ k < 4, g k ∈ rK := fun k hk => mem_rK hP (hA k hk).1
  let W : Set (Equiv.Perm (Fin 1408)) :=
    {x | x ∈ rK ∧ (x ∈ dK ∧ ∀ k < 4, x * g k = g k * x)}
  have hW : W.ncard = 8 := by
    have e := ncard_cntN hP (by norm_num) rRows rGen_lt (F := fun r => zgF 4 r (cdOf RR r))
      (Q := fun x => x ∈ dK ∧ ∀ k < 4, x * g k = g k * x) (fun r hr => by
        unfold zgF
        rw [bAnd_iff, inD_iff hP hr, allN_iffT]
        exact and_congr Iff.rfl (forall₂_congr fun k hk =>
          commC_iff hP (cd_lt_R hr) (cd_lt_R (hA k hk).1)))
    exact e.trans (cnt_eq 10 ch441697.cnt10)
  have hZW : (centerOf dK : Set (Equiv.Perm (Fin 1408))) = W := by
    apply Set.eq_of_subset_of_ncard_le
    · intro x hx
      have hx' : x ∈ centerOf dK := hx
      refine ⟨zD_le_R hP hx', hx'.1, fun k hk => ?_⟩
      exact (mem_centralizer_iff.1 hx'.2 _ (hgD k hk)).symm
    · rw [hW, ← Nat.card_coe_set_eq]
      exact (card_zD hP).ge
    · exact Set.toFinite _
  apply le_antisymm
  · intro x hx
    refine ⟨⟨hx.1, zD_le_R hP hx⟩, mem_centralizer_iff.2 fun h hh => ?_⟩
    exact mem_centralizer_iff.1 hx.2 h hh.1
  · intro x hx
    have hxW : x ∈ W := ⟨hx.1.2, hx.1.1, fun k hk =>
      (mem_centralizer_iff.1 hx.2 _ ⟨hgD k hk, hgR k hk⟩).symm⟩
    rw [← hZW] at hxW
    exact hxW

theorem zD_iso (hP : Nat.card ↥P1408 = 177408000) :
    Nonempty (↥(centerOf dK) ≃* Z 2 × Z 4) := by
  classical
  obtain ⟨-, -, b58, b59, n4, p4, n0, p2, q2⟩ := z_parts
  have h4 := zc_lt b58
  have h2 := zc_lt b59
  have m4 := (zD_list hP _).2 ⟨_, b58, rfl⟩
  have m2 := (zD_list hP _).2 ⟨_, b59, rfl⟩
  have e4 := elC_mem hP h4
  have e2 := elC_mem hP h2
  let x : ↥(centerOf dK) := ⟨_, m4⟩
  let y : ↥(centerOf dK) := ⟨_, m2⟩
  have hx2 : elC (zc (nm 58)) * elC (zc (nm 58)) ≠ 1 := by
    intro e
    have t := eqB_of_eq (g := elC (zc (nm 58)) * elC (zc (nm 58)))
      (f₁ := fun x => ev (zc (nm 58)) (ev (zc (nm 58)) x)) (f₂ := fun x => x)
      (fun _ hx => ev_ev h4 h4 hx) (fun x hx => by rw [e]; rfl)
    rw [n4] at t
    exact Bool.false_ne_true t
  have hx4 : elC (zc (nm 58)) * elC (zc (nm 58)) * elC (zc (nm 58)) * elC (zc (nm 58)) = 1 :=
    eq_of_eqB hP (mul_mem (mul_mem (mul_mem e4 e4) e4) e4) (one_mem _)
      (fun x hx => by rw [ev_elC h4 hx, ev_ev_ev h4 h4 h4 (Fin.isLt _)]; rfl) (fun _ _ => rfl) p4
  have hy1 : elC (zc (nm 59)) ≠ 1 := by
    intro e
    rw [← elC_zero] at e
    exact n0 (elC_inj h2 (by norm_num) e)
  have hy2 : elC (zc (nm 59)) * elC (zc (nm 59)) = 1 :=
    eq_of_eqB hP (mul_mem e2 e2) (one_mem _) (fun _ hx => ev_ev h2 h2 hx) (fun _ _ => rfl) p2
  have hyx : elC (zc (nm 59)) ≠ elC (zc (nm 58)) * elC (zc (nm 58)) := by
    intro e
    have t := eqB_of_eq (g := elC (zc (nm 59)))
      (f₁ := fun x => ev (zc (nm 59)) x) (f₂ := fun x => ev (zc (nm 58)) (ev (zc (nm 58)) x))
      (fun _ hx => ev_elC h2 hx) (fun x hx => by rw [e]; exact ev_ev h4 h4 hx)
    rw [q2] at t
    exact Bool.false_ne_true t
  have ox : orderOf x = 4 := by
    rw [← Subgroup.orderOf_coe]
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := elC (zc (nm 58)))
      (by rw [pow_one, pow_two]; exact hx2)
      (by
        simp only [pow_succ, pow_zero, pow_one, one_mul]
        exact hx4)
    rw [h]
    norm_num
  have oy : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  refine CFSG.EvenSporadicStandard.HNRecog.TwoHSData.nonempty_mulEquiv_two_four
    (fun a b => Subtype.ext ((mem_centralizer_iff.1 a.2.2 _ b.2.1).symm)) (card_zD hP) ox oy ?_
  intro hm
  rw [mem_zpowers_iff_mem_range_orderOf, ox, Finset.mem_image] at hm
  obtain ⟨n, hn, e⟩ := hm
  have e' : elC (zc (nm 58)) ^ n = elC (zc (nm 59)) := congrArg Subtype.val e
  have hn4 := Finset.mem_range.1 hn
  interval_cases n
  · exact hy1 (by rw [← e', pow_zero])
  · rw [pow_one] at e'
    rw [e'] at hx2
    exact hx2 hy2
  · rw [pow_two] at e'
    exact hyx e'.symm
  · apply hx2
    rw [← e', pow_three] at hy2
    calc elC (zc (nm 58)) * elC (zc (nm 58))
        = elC (zc (nm 58)) * elC (zc (nm 58)) *
            (elC (zc (nm 58)) * elC (zc (nm 58)) * elC (zc (nm 58)) * elC (zc (nm 58))) := by
          rw [hx4, mul_one]
      _ = elC (zc (nm 58)) * (elC (zc (nm 58)) * elC (zc (nm 58))) *
            (elC (zc (nm 58)) * (elC (zc (nm 58)) * elC (zc (nm 58)))) := by
          simp only [mul_assoc]
      _ = 1 := hy2

theorem hCD_K (hP : Nat.card ↥P1408 = 177408000) :
    dK ⊓ rK ⊓ centralizer ({elC (nm 60)} : Set (Equiv.Perm (Fin 1408))) = centerOf dK := by
  have hz := (sig_facts hP).2.2.2.2.2.2
  symm
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [(card_sig hP).2, card_zD hP])
  obtain ⟨k, hk, rfl⟩ := (zD_list hP x).1 hx
  exact ⟨⟨hx.1, zD_le_R hP hx⟩, mem_centralizer_singleton_iff.2 (hz k hk (zc_lt hk))⟩

theorem hCR_K (hP : Nat.card ↥P1408 = 177408000) :
    rK ⊓ centralizer ({elC (nm 60)} : Set (Equiv.Perm (Fin 1408))) =
      closure ((centerOf dK : Set (Equiv.Perm (Fin 1408))) ∪ {elemB}) := by
  obtain ⟨-, -, -, -, -, hbs, hz⟩ := sig_facts hP
  obtain ⟨h62, fb, hbR, -⟩ := named_facts hP
  have hle : closure ((centerOf dK : Set (Equiv.Perm (Fin 1408))) ∪ {elemB}) ≤
      rK ⊓ centralizer ({elC (nm 60)} : Set (Equiv.Perm (Fin 1408))) := by
    rw [closure_le]
    rintro x (hx | hx)
    · obtain ⟨k, hk, rfl⟩ := (zD_list hP x).1 hx
      exact ⟨zD_le_R hP hx, mem_centralizer_singleton_iff.2 (hz k hk (zc_lt hk))⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨hbR, mem_centralizer_singleton_iff.2 hbs⟩
  have hZC : centerOf dK ≤ closure ((centerOf dK : Set (Equiv.Perm (Fin 1408))) ∪ {elemB}) :=
    fun x hx => subset_closure (Or.inl hx)
  have hbC : elemB ∈ closure ((centerOf dK : Set (Equiv.Perm (Fin 1408))) ∪ {elemB}) :=
    subset_closure (Or.inr rfl)
  have hbZ : elemB ∉ centerOf dK := by
    intro hb
    obtain ⟨k, hk, e⟩ := (zD_list hP _).1 hb
    rw [← fb] at e
    exact (z_parts.2.1 k hk).2.2.2.2 (elC_inj (zc_lt hk) h62 e)
  have hdvd := Subgroup.card_dvd_of_le hZC
  rw [card_zD hP] at hdvd
  obtain ⟨j, hj⟩ := hdvd
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have hj1 : j ≤ 1 := by omega
    have hpos : 0 < Nat.card ↥(closure ((centerOf dK : Set (Equiv.Perm (Fin 1408))) ∪ {elemB})) :=
      Nat.card_pos
    have e := Subgroup.eq_of_le_of_card_ge hZC (by rw [hj, card_zD hP]; nlinarith)
    exact hbZ (e ▸ hbC)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [(card_sig hP).1, hj]
  omega

end CFSG.KD.HN1408.TabX

end
