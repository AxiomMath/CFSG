
module

public import Certificates.Kernel.Fin76bAut.Card
public import Certificates.Kernel.Fin76bAut.Checks
public import CFSG.Certificates.Kernel.Fin76bAut.Rec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Sound

public section

namespace CertificateChecks.KernelFin76bAut

open CFSG.KS.EAut CFSG.KS.PEnum CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.Fin76b.AutETable CFSG.EvenSporadicStandard.Fin76b.W16

theorem ch24614RecPt :
    ∀ i < 1920, penumPtK 32 6 63 192 false G G 5 1920 T PL POS SRT SRI i = true := by
  intro i hi
  have s0 := penumSlK_spec ch24614Rec0
  have s1 := penumSlK_spec ch24614Rec1
  have s2 := penumSlK_spec ch24614Rec2
  have s3 := penumSlK_spec ch24614Rec3
  rcases Nat.lt_or_ge i 480 with h0 | h0
  · simpa using s0 i h0 (by omega)
  rcases Nat.lt_or_ge i 960 with h1 | h1
  · have := s1 (i - 480) (by omega) (by omega)
    rwa [show 480 + (i - 480) = i by omega] at this
  rcases Nat.lt_or_ge i 1440 with h2 | h2
  · have := s2 (i - 960) (by omega) (by omega)
    rwa [show 960 + (i - 960) = i by omega] at this
  · have := s3 (i - 1440) (by omega) (by omega)
    rwa [show 1440 + (i - 1440) = i by omega] at this

theorem rec_all_of_realizes {H : Type*} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H}
    (R : Realizes H 32 M elt) (hM : ∀ a < 32, ∀ b < 32, mt M a b = mulE0 a b) :
    (∀ φ : MulAut H, ∃ i < 1920, ∀ a < 32, sg R φ a = eG (T i) a) ∧
    (∀ i < 1920, ∃ φ : MulAut H, ∀ a < 32, sg R φ a = eG (T i) a) ∧
    Nat.card (MulAut H) = 1920 :=
  recAll_of_checks R (fun a ha b hb => (hM a ha b hb).trans (eTabK_spec ch24614Tab a ha b hb).symm)
    ch24614Hd ch24614RecPt (card_mulAut_le_of_realizes R hM)

theorem rec_all_of_labelling {G : Type*} [Group G] {E : Subgroup G} {t : G} {tI : ℕ}
    {eltE : ℕ → G} (hL : ELabelling E t mulE0 tI eltE) :
    (∀ φ : MulAut ↥E, ∃ i < 1920, ∀ a (ha : a < 32),
      (φ ⟨eltE a, hL.mem a ha⟩ : G) = eltE (eG (T i) a)) ∧
    (∀ i < 1920, ∃ φ : MulAut ↥E, ∀ a (ha : a < 32),
      (φ ⟨eltE a, hL.mem a ha⟩ : G) = eltE (eG (T i) a)) ∧
    Nat.card (MulAut ↥E) = 1920 := by
  obtain ⟨elt, R, helt⟩ := E69.realizes_of_labelling hL
  obtain ⟨hmem, hex, hcard⟩ := rec_all_of_realizes R fun a ha b hb => mt_tab2 mulE0 ha hb
  have hact : ∀ (φ : MulAut ↥E) (a : ℕ) (ha : a < 32),
      (φ ⟨eltE a, hL.mem a ha⟩ : G) = eltE (sg R φ a) := by
    intro φ a ha
    have he : (⟨eltE a, hL.mem a ha⟩ : ↥E) = elt a := Subtype.ext (helt a ha).symm
    rw [he, ← sg_elt R φ a, helt _ (sg_lt R φ a)]
  refine ⟨fun φ => ?_, fun i hi => ?_, hcard⟩
  · obtain ⟨i, hi, h⟩ := hmem φ
    exact ⟨i, hi, fun a ha => by rw [hact φ a ha, h a ha]⟩
  · obtain ⟨φ, h⟩ := hex i hi
    exact ⟨φ, fun a ha => by rw [hact φ a ha, h a ha]⟩

end CertificateChecks.KernelFin76bAut

end
