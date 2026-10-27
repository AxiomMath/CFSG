module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Kernel.HN.Words
public import Certificates.Kernel.HN.Dce
public import Certificates.Kernel.HN.Tables
import CFSG.Certificates.Kernel.Bounds.HNAlt.RelsTC
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.Finite
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.Kernel.DceSPSound

public section

namespace CertificateChecks.KernelBounds

open CFSG.Certificates CFSG.KC.HNA CFSG.KC.HNA.DceS CertificateChecks.KernelBounds.HNW

theorem mem_normalizer_zpowers {G : Type*} [Group G] {g t : G} [Finite (Subgroup.zpowers t)]
    (h1 : g * t * g⁻¹ ∈ Subgroup.zpowers t) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  have hle : (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers t := by
    rw [Subgroup.map_le_iff_le_comap]
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_comap]
    change g * t ^ k * g⁻¹ ∈ Subgroup.zpowers t
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 k
  have hcard := Subgroup.card_map_of_injective (K := Subgroup.zpowers t)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← heq]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨x, hx, hxe⟩ := hh
    have : x = h := by
      change g * x * g⁻¹ = g * h * g⁻¹ at hxe
      simpa using hxe
    rwa [← this]

theorem card_sup_le {G : Type*} [Group G] {K T : Subgroup G} [Finite K] [Finite T]
    (hKT : K ≤ Subgroup.normalizer (T : Set G)) : Finite (K ⊔ T : Subgroup G) ∧
      Nat.card (K ⊔ T : Subgroup G) ≤ Nat.card K * Nat.card T := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right K T hKT
  let f : K × T → (K ⊔ T : Subgroup G) := fun p => ⟨p.1.1 * p.2.1, by
    rw [← SetLike.mem_coe, hset]
    exact Set.mul_mem_mul p.1.2 p.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [← SetLike.mem_coe, hset] at hz
    obtain ⟨k, hk, t, ht, rfl⟩ := hz
    exact ⟨(⟨k, hk⟩, ⟨t, ht⟩), rfl⟩
  exact ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans_eq (Nat.card_prod K T)⟩

theorem hn_rels_len : CFSG.KC.HNA.rels.length = 19 := rfl

theorem hn_rels_small : ∀ w ∈ CFSG.KC.HNA.rels, w.length < 1024 ∧ ∀ p ∈ w, p.1 < 5 := by
  decide

theorem hn_rel_eq (k : ℕ) (hk : k < 19) :
    CFSG.KC.HNA.rel k = encEnt (CFSG.KC.HNA.rels[k]'(by rw [hn_rels_len]; exact hk)) := by
  have hl := eqL_eq _ _ CFSG.KC.HNA.list_bind
  have hlen : CFSG.KC.HNA.list.length = 19 := rfl
  have e : CFSG.KC.HNA.rel k = CFSG.KC.HNA.list[k]'(by rw [hlen]; exact hk) := by
    interval_cases k <;> rfl
  rw [e]
  have key : ∀ (L : List ℕ) (hL : L = encList CFSG.KC.HNA.rels) (h1 : k < L.length)
      (h2 : k < CFSG.KC.HNA.rels.length), L[k]'h1 = encEnt (CFSG.KC.HNA.rels[k]'h2) := by
    rintro L rfl h1 h2
    simp only [encList_eq, List.getElem_map]
  exact key _ hl _ _

theorem hn_isN (c : ℕ) (hc : c < 8) : isN CFSG.KD.HNA.TL CFSG.KD.HNA.VL CFSG.KD.HNA.NL c = true := by
  interval_cases c <;> rfl

theorem hn_LI (c : ℕ) (hc : c < 8) : byte CFSG.KD.HNA.LI c = Nat.xor c 1 := by
  interval_cases c <;> rfl

theorem hn_letCode (g : ℕ) (b : Bool) (hg : g < 5) :
    letCode (g, b) = if g = 3 then 8 else Bool.rec (2 * (if g = 4 then 3 else g) + 1)
      (2 * (if g = 4 then 3 else g)) b := by
  interval_cases g <;> cases b <;> rfl

theorem hn_control : ∀ (H : Type) [Group H] (y : ℕ → H),
    (∀ r < CFSG.KD.HNA.NR, DSP.nOnly CFSG.KD.HNA.TL CFSG.KD.HNA.VL CFSG.KD.HNA.NL
      (CFSG.KC.HNA.rel r) → DSP.rval y (CFSG.KC.HNA.rel r) = 1) →
    (∀ c < CFSG.KD.HNA.NL, isN CFSG.KD.HNA.TL CFSG.KD.HNA.VL CFSG.KD.HNA.NL c = true →
      y (byte CFSG.KD.HNA.LI c) = (y c)⁻¹) →
    Finite (Subgroup.closure (y '' {c | c < CFSG.KD.HNA.NL ∧
        isN CFSG.KD.HNA.TL CFSG.KD.HNA.VL CFSG.KD.HNA.NL c = true})) ∧
      Nat.card (Subgroup.closure (y '' {c | c < CFSG.KD.HNA.NL ∧
        isN CFSG.KD.HNA.TL CFSG.KD.HNA.VL CFSG.KD.HNA.NL c = true})) ≤ CFSG.KD.HNA.NORD := by
  intro H _ y hrelN hinvN
  have hNL : CFSG.KD.HNA.NL = 9 := rfl
  have hNR : CFSG.KD.HNA.NR = 19 := rfl
  have hinv' : ∀ c < 8, y (Nat.xor c 1) = (y c)⁻¹ := fun c hc => by
    rw [← hn_LI c hc]
    exact hinvN c (by omega) (hn_isN c hc)
  let gen : ℕ → H := fun g => y (letCode (g, true))
  have hlet : ∀ p : ℕ × Bool, p.1 < 5 → p.1 ≠ 3 →
      y (letCode p) = if p.2 then gen p.1 else (gen p.1)⁻¹ := by
    rintro ⟨g, b⟩ hg h3
    simp only at hg h3 ⊢
    cases b
    · simp only [gen, Bool.false_eq_true, ↓reduceIte]
      interval_cases g
      · exact hinv' 0 (by norm_num)
      · exact hinv' 2 (by norm_num)
      · exact hinv' 4 (by norm_num)
      · exact absurd rfl h3
      · exact hinv' 6 (by norm_num)
    · simp [gen]
  have hrelsD : ∀ r ∈ CFSG.KC.HNA.rels, (∀ x ∈ r, x.1 ≠ 3) → KB.sword gen r = 1 := by
    intro r hr hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨hlen, hsm⟩ := hn_rels_small _ hr
    have hk' : k < 19 := by rw [← hn_rels_len]; exact hk
    have hN : DSP.nOnly CFSG.KD.HNA.TL CFSG.KD.HNA.VL CFSG.KD.HNA.NL (CFSG.KC.HNA.rel k) := by
      rw [hn_rel_eq k hk']
      apply nOnly_encEnt _ _ _ _ hlen
      intro p hp
      apply hn_isN
      obtain ⟨g, b⟩ := p
      have h5 := hsm _ hp
      have h3 := hx _ hp
      simp only at h5 h3
      rw [hn_letCode g b h5]
      interval_cases g <;> cases b <;> simp_all
    have := hrelN k (by rw [hNR]; exact hk') hN
    rw [hn_rel_eq k hk', rval_encEnt y _ hlen] at this
    rw [← this, KB.sword]
    congr 1
    apply List.map_congr_left
    intro p hp
    exact (hlet p (hsm p hp) (hx p hp)).symm
  have top4 : KB.topOk CFSG.KC.HNA.N5A.T4.amap 2 = true := by quickRfl
  have t3 := CertificateChecks.KernelBounds.HN.t3
  have t4 := CertificateChecks.KernelBounds.HN.t4
  have s3 := KB.tableOk_sound_alpha gen (fun r hr hx => hrelsD r hr fun x hxr => by
    have : x.1 < 3 := (KB.topOk_sound (by norm_num) CFSG.KC.HNA.N5A.top x.1).mp (hx x hxr)
    omega) t3
  have s4 := KB.tableOk_sound_alpha gen (fun r hr hx => hrelsD r hr fun x hxr => by
    have : x.1 < 2 := (KB.topOk_sound (by norm_num) top4 x.1).mp (hx x hxr)
    omega) t4
  rw [KB.linkOk_sound gen (KB.tableOk_lens t3).2 CFSG.KC.HNA.N5A.link_T3] at s3
  rw [show CFSG.KC.HNA.N5A.T4.words = [] from rfl, KB.wordSub_nil] at s4
  have cK := KB.card_le_step s3 (KB.card_le_step s4 KB.card_bot_le)
  set K := KB.alphaSub gen CFSG.KC.HNA.N5A.T3.amap
  have hKmem : ∀ g < 3, gen g ∈ K := fun g hg => Subgroup.subset_closure
    ⟨g, (KB.topOk_sound (by norm_num) CFSG.KC.HNA.N5A.top g).mpr hg, rfl⟩
  have : Finite K := Nat.finite_of_card_ne_zero cK.1
  set t := y 6
  have ht : gen 4 = t := rfl
  have r14 : CFSG.KC.HNA.rels[14] = [(4, true), (4, true), (4, true), (4, true), (4, true)] := rfl
  have r15 : CFSG.KC.HNA.rels[15] = [(0, false), (4, true), (0, true), (4, true), (4, true)] := rfl
  have r16 : CFSG.KC.HNA.rels[16] = [(2, false), (4, true), (2, true), (4, false), (4, false)] := rfl
  have r17 : CFSG.KC.HNA.rels[17] = [(4, false), (1, false), (4, true), (1, true)] := rfl
  have h14 := hrelsD _ (List.getElem_mem (l := CFSG.KC.HNA.rels) (n := 14) (by decide))
    (by rw [r14]; decide)
  have h15 := hrelsD _ (List.getElem_mem (l := CFSG.KC.HNA.rels) (n := 15) (by decide))
    (by rw [r15]; decide)
  have h16 := hrelsD _ (List.getElem_mem (l := CFSG.KC.HNA.rels) (n := 16) (by decide))
    (by rw [r16]; decide)
  have h17 := hrelsD _ (List.getElem_mem (l := CFSG.KC.HNA.rels) (n := 17) (by decide))
    (by rw [r17]; decide)
  rw [r14, KB.sword] at h14
  rw [r15, KB.sword] at h15
  rw [r16, KB.sword] at h16
  rw [r17, KB.sword] at h17
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ↓reduceIte,
    Bool.false_eq_true, ht, mul_one] at h14 h15 h16 h17
  have ht5 : t ^ 5 = 1 := by
    rw [← h14]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  set T := Subgroup.zpowers t
  have hTmem : ∀ k : ℤ, t ^ k ∈ T := fun k => ⟨k, rfl⟩
  have hTc : Nat.card T ≤ 5 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) ht5
  have : Finite T := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, ht5⟩)).ne')
  have hnorm : K ≤ Subgroup.normalizer (T : Set H) := by
    change Subgroup.closure (gen '' {g | KB.inAlpha CFSG.KC.HNA.N5A.T3.amap g}) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg3 : g < 3 := (KB.topOk_sound (by norm_num) CFSG.KC.HNA.N5A.top g).mp hg
    have htt : t * t ∈ T := Subgroup.mul_mem _ (Subgroup.mem_zpowers t) (Subgroup.mem_zpowers t)
    rw [SetLike.mem_coe, ← inv_mem_iff]
    apply mem_normalizer_zpowers
    rw [inv_inv]
    interval_cases g
    ·
      have e : (gen 0)⁻¹ * t * gen 0 * (t * t) = 1 := by simpa only [mul_assoc] using h15
      rw [eq_inv_of_mul_eq_one_left e]
      exact inv_mem htt
    ·
      have e : t⁻¹ * ((gen 1)⁻¹ * t * gen 1) = 1 := by simpa only [mul_assoc] using h17
      rw [eq_inv_of_mul_eq_one_right e, inv_inv]
      exact Subgroup.mem_zpowers t
    ·
      have e : (gen 2)⁻¹ * t * gen 2 * (t⁻¹ * t⁻¹) = 1 := by simpa only [mul_assoc] using h16
      rw [eq_inv_of_mul_eq_one_left e, mul_inv_rev, inv_inv]
      exact htt
  obtain ⟨hSf, hSc⟩ := card_sup_le hnorm
  have hle : Subgroup.closure (y '' {c | c < CFSG.KD.HNA.NL ∧
      isN CFSG.KD.HNA.TL CFSG.KD.HNA.VL CFSG.KD.HNA.NL c = true}) ≤ K ⊔ T := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, ⟨hc, hcN⟩, rfl⟩
    rw [hNL] at hc
    have hc8 : c < 8 := by
      by_contra h
      have : c = 8 := by omega
      subst this
      exact absurd hcN (by decide)
    have hK : ∀ g < 3, y (2 * g) ∈ K ⊔ T := fun g hg =>
      Subgroup.mem_sup_left (by
        have := hKmem g hg
        simp only [gen] at this
        rw [hn_letCode g true (by omega)] at this
        interval_cases g <;> simpa using this)
    interval_cases c
    · exact hK 0 (by norm_num)
    · rw [show (1 : ℕ) = Nat.xor 0 1 from rfl, hinv' 0 (by norm_num)]
      exact inv_mem (hK 0 (by norm_num))
    · exact hK 1 (by norm_num)
    · rw [show (3 : ℕ) = Nat.xor 2 1 from rfl, hinv' 2 (by norm_num)]
      exact inv_mem (hK 1 (by norm_num))
    · exact hK 2 (by norm_num)
    · rw [show (5 : ℕ) = Nat.xor 4 1 from rfl, hinv' 4 (by norm_num)]
      exact inv_mem (hK 2 (by norm_num))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    · rw [show (7 : ℕ) = Nat.xor 6 1 from rfl, hinv' 6 (by norm_num)]
      exact inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hNORD : CFSG.KD.HNA.NORD =
      CFSG.KC.HNA.N5A.tOrd * CFSG.KC.HNA.N5A.T3.N * CFSG.KC.HNA.N5A.T4.N :=
    Nat.beq_eq.mp CFSG.KC.HNA.N5A.nord
  refine ⟨Finite.of_injective _ (Subgroup.inclusion_injective hle), ?_⟩
  calc _ ≤ Nat.card (K ⊔ T : Subgroup H) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card K * Nat.card T := hSc
    _ ≤ (CFSG.KC.HNA.N5A.T3.N * (CFSG.KC.HNA.N5A.T4.N * 1)) * 5 := Nat.mul_le_mul cK.2 hTc
    _ = CFSG.KD.HNA.NORD := by
      rw [hNORD, show CFSG.KC.HNA.N5A.tOrd = 5 from rfl]
      ring

theorem hn_gens : TauCeti.Sporadic.hnPresentation.generatorCount = 5 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.hnPresentation_generatorNames]

noncomputable def hnX (c : ℕ) : TauCeti.Sporadic.hnPresentation.Group :=
  if c = 8 then KB.tcGen TauCeti.Sporadic.hnPresentation 3
  else if c % 2 = 0 then KB.tcGen TauCeti.Sporadic.hnPresentation (if c / 2 = 3 then 4 else c / 2)
  else (KB.tcGen TauCeti.Sporadic.hnPresentation (if c / 2 = 3 then 4 else c / 2))⁻¹

theorem hn : Finite TauCeti.SporadicName.HN.Group ∧
    Nat.card TauCeti.SporadicName.HN.Group ≤ 273030912000000 := by
  change Finite TauCeti.Sporadic.hnPresentation.Group ∧
    Nat.card TauCeti.Sporadic.hnPresentation.Group ≤ 273030912000000
  have hrelsP := KB.sword_rels TauCeti.Sporadic.hnPresentation CFSG.KC.HNA.rels_eq
  have hd : KB.tcGen TauCeti.Sporadic.hnPresentation 3 *
      KB.tcGen TauCeti.Sporadic.hnPresentation 3 = 1 := by
    have := hrelsP _ (List.getElem_mem (l := CFSG.KC.HNA.rels) (n := 10) (by decide))
    simpa [KB.sword, show CFSG.KC.HNA.rels[10] = [(3, true), (3, true)] from rfl] using this
  have hdi : (KB.tcGen TauCeti.Sporadic.hnPresentation 3)⁻¹ =
      KB.tcGen TauCeti.Sporadic.hnPresentation 3 := (eq_inv_of_mul_eq_one_left hd).symm
  have hlet : ∀ p : ℕ × Bool, p.1 < 5 →
      hnX (letCode p) = if p.2 then KB.tcGen TauCeti.Sporadic.hnPresentation p.1
        else (KB.tcGen TauCeti.Sporadic.hnPresentation p.1)⁻¹ := by
    rintro ⟨g, b⟩ hg
    simp only at hg ⊢
    rw [hn_letCode g b hg]
    interval_cases g <;> cases b <;> simp [hnX, hdi]
  have hrels : ∀ r < CFSG.KD.HNA.NR, DSP.rval hnX (CFSG.KC.HNA.rel r) = 1 := by
    intro k hk
    have hk' : k < 19 := hk
    have hmem := List.getElem_mem (l := CFSG.KC.HNA.rels) (n := k) (by rw [hn_rels_len]; exact hk')
    obtain ⟨hlen, hsm⟩ := hn_rels_small _ hmem
    rw [hn_rel_eq k hk', rval_encEnt hnX _ hlen, ← hrelsP _ hmem, KB.sword]
    congr 1
    apply List.map_congr_left
    intro p hp
    exact hlet p (hsm p hp)
  have hinv : ∀ c < CFSG.KD.HNA.NL, isN CFSG.KD.HNA.TL CFSG.KD.HNA.VL CFSG.KD.HNA.NL c = true →
      hnX (byte CFSG.KD.HNA.LI c) = (hnX c)⁻¹ := by
    intro c hc hN
    have hc9 : c < 9 := hc
    interval_cases c
    all_goals first
      | exact absurd hN (by decide)
      | (rw [show byte CFSG.KD.HNA.LI _ = _ from hn_LI _ (by norm_num)]; simp [hnX])
  have hu : hnX CFSG.KD.HNA.VL = (hnX CFSG.KD.HNA.TL)⁻¹ := by
    change hnX 8 = (hnX 8)⁻¹
    simp [hnX, hdi]
  obtain ⟨hf, hc⟩ := DSP.dceOk_sound CertificateChecks.KernelBounds.HN.dce_ok hn_control hnX hrels
    hinv hu
  have htop : Subgroup.closure (hnX '' {c | c < CFSG.KD.HNA.NL}) = ⊤ := by
    rw [eq_top_iff, ← KB.closure_tcGen TauCeti.Sporadic.hnPresentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [hn_gens] at hg
    have hmem : ∀ c < 9, hnX c ∈ Subgroup.closure (hnX '' {c | c < CFSG.KD.HNA.NL}) :=
      fun c hc => Subgroup.subset_closure ⟨c, hc, rfl⟩
    have hg5 : g < 5 := hg
    interval_cases g
    · simpa [hnX] using hmem 0 (by norm_num)
    · simpa [hnX] using hmem 2 (by norm_num)
    · simpa [hnX] using hmem 4 (by norm_num)
    · simpa [hnX] using hmem 8 (by norm_num)
    · simpa [hnX] using hmem 6 (by norm_num)
  rw [htop] at hf hc
  refine ⟨Finite.of_equiv _ Subgroup.topEquiv.toEquiv, ?_⟩
  rw [← Subgroup.card_top]
  exact hc.trans (Nat.le_of_ble_eq_true rfl)

end CertificateChecks.KernelBounds

end
