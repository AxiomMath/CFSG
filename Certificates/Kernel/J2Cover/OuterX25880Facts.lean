module

public import Certificates.Kernel.J2Cover.OuterX25880
public import Certificates.Kernel.Fin76bAut.Core
public import CFSG.Certificates.Kernel.TC2Outer0Sound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Table
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWIso2

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.EAut CFSG.ComponentClassification.J2Cover.Models
open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.J2

theorem mulX_eq_mulXK : mulX = mulXK := by
  funext a d
  unfold mulX mulXK mulJ2
  simp only [mt_pt]

theorem eListX_eq25880 : TableX.eListX 256 innX mulX 4 = EL25880 := by
  rw [mulX_eq_mulXK]
  exact of_decide_eq_true kEL25880

theorem getD_mem25880 {j : ℕ} (hj : j < 32) : SIG25880.getD j 0 ∈ SIG25880 := by
  rw [List.getD_eq_getElem _ _ (by simpa [SIG25880] using hj)]
  exact List.getElem_mem _

theorem card_aut25880 {G : Type*} [Group G] {elt : ℕ → G}
    (hinj : ∀ a b, a < 256 → b < 256 → elt a = elt b → a = b)
    (hmul : ∀ a b, a < 256 → b < 256 → mulX a b < 256 ∧ elt a * elt b = elt (mulX a b))
    (h0 : elt 0 = 1) (E : Subgroup G)
    (hE : ∀ x, x ∈ E ↔ ∃ a ∈ TableX.eListX 256 innX mulX 4, elt a = x)
    (hlt : ∀ a ∈ TableX.eListX 256 innX mulX 4, a < 256) : Nat.card (MulAut ↥E) = 1920 := by
  have hk := kLab25880
  simp only [lab25880, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, List.contains_iff_mem] at hk
  obtain ⟨⟨⟨⟨⟨⟨htab, hsub⟩, hsup⟩, -⟩, hnd⟩, hs0⟩, hs21⟩ := hk
  rw [eListX_eq25880] at hE hlt
  have hSlt : ∀ j < 32, SIG25880.getD j 0 < 256 := fun j hj => hlt _ (hsub _ (getD_mem25880 hj))
  have hL : ELabelling E (elt 4) W16.mulE0 21 (fun j => elt (SIG25880.getD j 0)) :=
    { mem := fun k hk => (hE _).2 ⟨_, hsub _ (getD_mem25880 hk), rfl⟩
      surj := by
        intro e he
        obtain ⟨a, ha, rfl⟩ := (hE e).1 he
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hsup a ha)
        refine ⟨j, by simpa [SIG25880] using hj, ?_⟩
        rw [List.getD_eq_getElem _ _ hj]
      inj := by
        intro a ha b hb h
        have e := hinj _ _ (hSlt a ha) (hSlt b hb) h
        have ha' : a < SIG25880.length := by simpa [SIG25880] using ha
        have hb' : b < SIG25880.length := by simpa [SIG25880] using hb
        rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at e
        exact (hnd.getElem_inj_iff).1 e
      lt := CFSG.EvenSporadicStandard.Fin76b.W16.mulE0_lt
      mul := by
        intro a ha b hb
        rw [KernelFin76bAut.ch24614ET a ha b hb, htab a ha b hb, ← mulX_eq_mulXK]
        exact ((hmul _ _ (hSlt a ha) (hSlt b hb)).2).symm
      one := by rw [hs0, h0]
      tI_lt := by norm_num
      at_tI := by rw [hs21] }
  exact (KernelFin76bAut.rec_all_of_labelling hL).2.2

theorem outerFacts25880 {Y : Type} [Group Y] [Finite (MulAut Y)] (elt : ℕ → MulAut Y) (t : Y)
    (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hinj : ∀ a b, a < 256 → b < 256 → elt a = elt b → a = b)
    (hmul : ∀ a b, a < 256 → b < 256 → mulX a b < 256 ∧ elt a * elt b = elt (mulX a b))
    (h0 : elt 0 = 1) (h4 : elt 4 = MulAut.conj t)
    (hInn : ∀ a, a < 128 → ∃ y : Y, elt a = MulAut.conj y)
    (hconj : ∀ a ∈ TableX.eListX 256 innX mulX 4, mulX a a = 0 → a ≠ 0 →
      ∃ c : Y, elt a = MulAut.conj (c * t * c⁻¹)) :
    ∃ K E : Subgroup (MulAut Y), OuterEFacts Y K t E := by
  have hspec : TableX.CheckSpec0 256 innX mulX 4 := by
    rw [mulX_eq_mulXK]
    exact CFSG.KC.TC2Outer.checkSpec0_of_check0 kOuter25880
  obtain ⟨K, E, hf, -⟩ := exists_outerEFacts_of_card ht2 ht1 hinj hmul h0 ⟨by norm_num, h4⟩
    (fun a _ hinn => hInn a (by simpa [innX] using hinn)) (fun a _ _ hm => hconj a hm) hspec
    (card_aut25880 hinj hmul h0)
  exact ⟨K, E, hf⟩

theorem fixFacts25880 : ∀ a ∈ TableX.eListX 256 innX mulX 4,
    a < 128 ∧ (mulX a a = 0 → a ≠ 0 → fixCountArr eltArrs[a]! = 11) := by
  rw [eListX_eq25880, mulX_eq_mulXK]
  intro a ha
  have h := List.all_eq_true.1 kFix25880 a ha
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq, beq_iff_eq] at h
  obtain ⟨halt, hf⟩ := h
  refine ⟨halt, fun hsq h0 => ?_⟩
  rw [eltArrs_eq a halt, fixCount_unpack]
  rcases hf with (h | h) | h
  · exact absurd hsq h
  · exact absurd h h0
  · exact h

end CertificateChecks.KernelJ2Cover

end
