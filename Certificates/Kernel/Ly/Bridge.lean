module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Kernel.Ly.Words
public import Certificates.Kernel.Ly.Dce
public import Certificates.Kernel.Ly.Tables
import CFSG.Certificates.Kernel.Bounds.LyAlt.RelsTC
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.Kernel.DceS5Sound
public import CFSG.Certificates.Kernel.DceSPSound
public import CFSG.Open.Defs
public import Certificates.Kernel.HN.Words

public section

namespace CertificateChecks.KernelBounds

open CFSG.Certificates CFSG.KC.LyA CFSG.KC.LyA.DceS CertificateChecks.KernelBounds.LyW

theorem ly_rels_len : CFSG.KC.LyA.rels.length = 53 := rfl

theorem ly_rels_smallB : smallB CFSG.KC.LyA.rels 6 = true := by quickRfl

theorem ly_rels_small : ∀ w ∈ CFSG.KC.LyA.rels, w.length < 1024 ∧ ∀ p ∈ w, p.1 < 6 :=
  smallB_spec 6 _ ly_rels_smallB

theorem ly_rel_eq (k : ℕ) (hk : k < 53) :
    CFSG.KC.LyA.rel k = encEnt (CFSG.KC.LyA.rels[k]'(by rw [ly_rels_len]; exact hk)) := by
  have hl := eqL_eq _ _ CFSG.KC.LyA.list_bind
  have hlen : CFSG.KC.LyA.list.length = 53 := rfl
  have e : CFSG.KC.LyA.rel k = CFSG.KC.LyA.list[k]'(by rw [hlen]; exact hk) := by
    interval_cases k <;> rfl
  rw [e]
  have key : ∀ (L : List ℕ) (hL : L = encList CFSG.KC.LyA.rels) (h1 : k < L.length)
      (h2 : k < CFSG.KC.LyA.rels.length), L[k]'h1 = encEnt (CFSG.KC.LyA.rels[k]'h2) := by
    rintro L rfl h1 h2
    simp only [encList_eq, List.getElem_map]
  exact key _ hl _ _

theorem ly_isN (c : ℕ) (hc : c < 10) : isN CFSG.KD.LyA.TL CFSG.KD.LyA.VL CFSG.KD.LyA.NL c = true := by
  interval_cases c <;> rfl

theorem ly_LI (g : ℕ) (hg : g < 5) :
    byte CFSG.KD.LyA.LI (2 * g) = 2 * g + 1 ∧ byte CFSG.KD.LyA.LI (2 * g + 1) = 2 * g := by
  interval_cases g <;> exact ⟨rfl, rfl⟩

theorem ly_control : ∀ (H : Type) [Group H] (y : ℕ → H),
    (∀ r < CFSG.KD.LyA.NR, DS5.nOnly CFSG.KD.LyA.TL CFSG.KD.LyA.VL CFSG.KD.LyA.NL
      (CFSG.KC.LyA.rel r) → DS5.rval y (CFSG.KC.LyA.rel r) = 1) →
    (∀ c < CFSG.KD.LyA.NL, isN CFSG.KD.LyA.TL CFSG.KD.LyA.VL CFSG.KD.LyA.NL c = true →
      y (byte CFSG.KD.LyA.LI c) = (y c)⁻¹) →
    Finite (Subgroup.closure (y '' {c | c < CFSG.KD.LyA.NL ∧
        isN CFSG.KD.LyA.TL CFSG.KD.LyA.VL CFSG.KD.LyA.NL c = true})) ∧
      Nat.card (Subgroup.closure (y '' {c | c < CFSG.KD.LyA.NL ∧
        isN CFSG.KD.LyA.TL CFSG.KD.LyA.VL CFSG.KD.LyA.NL c = true})) ≤ CFSG.KD.LyA.NORD := by
  intro H _ y hrelN hinvN
  have hNL : CFSG.KD.LyA.NL = 12 := rfl
  have hNR : CFSG.KD.LyA.NR = 53 := rfl
  have hinv' : ∀ g < 5, y (2 * g + 1) = (y (2 * g))⁻¹ := fun g hg => by
    rw [← (ly_LI g hg).1]
    exact hinvN (2 * g) (by omega) (ly_isN _ (by omega))
  let gen : ℕ → H := fun g => y (2 * g)
  have hlet : ∀ p : ℕ × Bool, p.1 < 5 →
      y (letCode p) = if p.2 then gen p.1 else (gen p.1)⁻¹ := by
    rintro ⟨g, b⟩ hg
    simp only at hg ⊢
    rw [letCode_eq]
    cases b
    · simpa [gen] using hinv' g hg
    · simp [gen]
  have hrelsZ : ∀ r ∈ CFSG.KC.LyA.rels, (∀ x ∈ r, x.1 < 5) → KB.sword gen r = 1 := by
    intro r hr hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨hlen, hsm⟩ := ly_rels_small _ hr
    have hk' : k < 53 := by rw [← ly_rels_len]; exact hk
    have h128 : ∀ p ∈ CFSG.KC.LyA.rels[k], p.1 < 128 := fun p hp => by
      have := hsm p hp
      omega
    have hN : DS5.nOnly CFSG.KD.LyA.TL CFSG.KD.LyA.VL CFSG.KD.LyA.NL (CFSG.KC.LyA.rel k) := by
      rw [ly_rel_eq k hk']
      apply nOnly_encEnt _ _ _ _ hlen h128
      intro p hp
      apply ly_isN
      obtain ⟨g, b⟩ := p
      have h5 := hx _ hp
      simp only at h5
      rw [letCode_eq]
      cases b <;> simp <;> omega
    have := hrelN k (by rw [hNR]; exact hk') hN
    rw [ly_rel_eq k hk', rval_encEnt y _ hlen h128] at this
    rw [← this, KB.sword]
    congr 1
    apply List.map_congr_left
    intro p hp
    exact (hlet p (hx p hp)).symm
  have top3 : KB.topOk CFSG.KC.LyA.G25.T3.amap 3 = true := by quickRfl
  have top4 : KB.topOk CFSG.KC.LyA.G25.T4.amap 2 = true := by quickRfl
  have s2 := KB.tableOk_sound_alpha gen (fun r hr hx => hrelsZ r hr fun x hxr => by
    have : x.1 < 5 := (KB.topOk_sound (by norm_num) CFSG.KC.LyA.G25.top x.1).mp (hx x hxr)
    exact this) CertificateChecks.KernelBounds.Ly.t2
  have s3 := KB.tableOk_sound_alpha gen (fun r hr hx => hrelsZ r hr fun x hxr => by
    have : x.1 < 3 := (KB.topOk_sound (by norm_num) top3 x.1).mp (hx x hxr)
    omega) CertificateChecks.KernelBounds.Ly.t3
  have s4 := KB.tableOk_sound_alpha gen (fun r hr hx => hrelsZ r hr fun x hxr => by
    have : x.1 < 2 := (KB.topOk_sound (by norm_num) top4 x.1).mp (hx x hxr)
    omega) CertificateChecks.KernelBounds.Ly.t4
  rw [KB.linkOk_sound gen (KB.tableOk_lens CertificateChecks.KernelBounds.Ly.t2).2
    CFSG.KC.LyA.G25.link_T2] at s2
  rw [KB.linkOk_sound gen (KB.tableOk_lens CertificateChecks.KernelBounds.Ly.t3).2
    CFSG.KC.LyA.G25.link_T3] at s3
  rw [show CFSG.KC.LyA.G25.T4.words = [] from rfl, KB.wordSub_nil] at s4
  have cK := KB.card_le_step s2 (KB.card_le_step s3 (KB.card_le_step s4 KB.card_bot_le))
  set K := KB.alphaSub gen CFSG.KC.LyA.G25.T2.amap
  have hKmem : ∀ g < 5, gen g ∈ K := fun g hg => Subgroup.subset_closure
    ⟨g, (KB.topOk_sound (by norm_num) CFSG.KC.LyA.G25.top g).mpr hg, rfl⟩
  have : Finite K := Nat.finite_of_card_ne_zero cK.1
  have hle : Subgroup.closure (y '' {c | c < CFSG.KD.LyA.NL ∧
      isN CFSG.KD.LyA.TL CFSG.KD.LyA.VL CFSG.KD.LyA.NL c = true}) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, ⟨hc, hcN⟩, rfl⟩
    rw [hNL] at hc
    have hc10 : c < 10 := by
      by_contra h
      have : c = 10 ∨ c = 11 := by omega
      rcases this with rfl | rfl <;> exact absurd hcN (by decide)
    rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
    · have : c = 2 * m := by omega
      subst this
      exact hKmem m (by omega)
    · have e : c = 2 * m + 1 := by omega
      rw [e, hinv' m (by omega)]
      exact inv_mem (hKmem m (by omega))
  have hNORD : CFSG.KD.LyA.NORD =
      CFSG.KC.LyA.G25.T2.N * CFSG.KC.LyA.G25.T3.N * CFSG.KC.LyA.G25.T4.N :=
    Nat.beq_eq.mp CFSG.KC.LyA.G25.nord
  refine ⟨Finite.of_injective _ (Subgroup.inclusion_injective hle), ?_⟩
  calc _ ≤ Nat.card K := Subgroup.card_le_of_le hle
    _ ≤ CFSG.KC.LyA.G25.T2.N * (CFSG.KC.LyA.G25.T3.N * (CFSG.KC.LyA.G25.T4.N * 1)) := cK.2
    _ = CFSG.KD.LyA.NORD := by
      rw [hNORD]
      ring

theorem ly_gens : TauCeti.Sporadic.Lyons.presentation.generatorCount = 6 := by
  simp [TauCeti.GroupPresentation.generatorCount,
    TauCeti.Sporadic.Lyons.presentation_generatorNames]

noncomputable def lyX (c : ℕ) : TauCeti.Sporadic.Lyons.presentation.Group :=
  if c % 2 = 0 then KB.tcGen TauCeti.Sporadic.Lyons.presentation (c / 2)
  else (KB.tcGen TauCeti.Sporadic.Lyons.presentation (c / 2))⁻¹

theorem ly : Finite TauCeti.SporadicName.Ly.Group ∧
    Nat.card TauCeti.SporadicName.Ly.Group ≤ 51765179004000000 := by
  change Finite TauCeti.Sporadic.Lyons.presentation.Group ∧
    Nat.card TauCeti.Sporadic.Lyons.presentation.Group ≤ 51765179004000000
  have hrelsP := KB.sword_rels TauCeti.Sporadic.Lyons.presentation CFSG.KC.LyA.rels_eq
  have hlet : ∀ p : ℕ × Bool, lyX (letCode p) =
      if p.2 then KB.tcGen TauCeti.Sporadic.Lyons.presentation p.1
      else (KB.tcGen TauCeti.Sporadic.Lyons.presentation p.1)⁻¹ := by
    rintro ⟨g, b⟩
    rw [letCode_eq]
    cases b <;> simp [lyX, Nat.add_mod, Nat.add_div]
  have hrels : ∀ r < CFSG.KD.LyA.NR, DS5.rval lyX (CFSG.KC.LyA.rel r) = 1 := by
    intro k hk
    have hk' : k < 53 := hk
    have hmem := List.getElem_mem (l := CFSG.KC.LyA.rels) (n := k) (by rw [ly_rels_len]; exact hk')
    obtain ⟨hlen, hsm⟩ := ly_rels_small _ hmem
    rw [ly_rel_eq k hk', rval_encEnt lyX _ hlen (fun p hp => by have := hsm p hp; omega),
      ← hrelsP _ hmem, KB.sword]
    congr 1
    apply List.map_congr_left
    intro p _
    exact hlet p
  have hinv : ∀ c < CFSG.KD.LyA.NL, isN CFSG.KD.LyA.TL CFSG.KD.LyA.VL CFSG.KD.LyA.NL c = true →
      lyX (byte CFSG.KD.LyA.LI c) = (lyX c)⁻¹ := by
    intro c hc hN
    have hc10 : c < 10 := by
      by_contra h
      have : c = 10 ∨ c = 11 := by
        have : c < 12 := hc
        omega
      rcases this with rfl | rfl <;> exact absurd hN (by decide)
    rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
    · have e : c = 2 * m := by omega
      subst e
      rw [(ly_LI m (by omega)).1]
      simp [lyX, Nat.add_mod, Nat.add_div]
    · have e : c = 2 * m + 1 := by omega
      subst e
      rw [(ly_LI m (by omega)).2]
      simp [lyX, Nat.add_mod, Nat.add_div]
  have hu : lyX CFSG.KD.LyA.VL = (lyX CFSG.KD.LyA.TL)⁻¹ := by
    change lyX 11 = (lyX 10)⁻¹
    simp [lyX]
  obtain ⟨hf, hc⟩ := DS5.dceOk_sound CertificateChecks.KernelBounds.Ly.dce_ok ly_control lyX hrels
    hinv hu
  have htop : Subgroup.closure (lyX '' {c | c < CFSG.KD.LyA.NL}) = ⊤ := by
    rw [eq_top_iff, ← KB.closure_tcGen TauCeti.Sporadic.Lyons.presentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg6 : g < 6 := by simpa [ly_gens] using hg
    have hmem : lyX (2 * g) ∈ Subgroup.closure (lyX '' {c | c < CFSG.KD.LyA.NL}) :=
      Subgroup.subset_closure ⟨2 * g, by change 2 * g < 12; omega, rfl⟩
    simpa [lyX] using hmem
  rw [htop] at hf hc
  refine ⟨Finite.of_equiv _ Subgroup.topEquiv.toEquiv, ?_⟩
  rw [← Subgroup.card_top]
  exact hc.trans (Nat.le_of_ble_eq_true rfl)

end CertificateChecks.KernelBounds

end
