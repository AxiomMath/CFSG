module

public import Certificates.Kernel.J4.Words
public import Certificates.Kernel.M24.Bridge
import Certificates.Kernel.J4.Assemble
import Certificates.Kernel.J4.ChecksFix
import Certificates.Kernel.J4.ChecksPts
import Certificates.Kernel.J4.ChecksMFix
import CFSG.Sporadic.Presentation.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelBounds

open CFSG.KJ4 CFSG.KJ4.R CFSG.KJ4.S CFSG.Certificates CFSG.Certificates.J4R CertificateChecks.KernelBounds.J4

theorem lift_mk_sword {H : Type*} [Group H] {n : ℕ} (gen : ℕ → H) (f : Fin n → H)
    (hf : ∀ i, f i = gen i.val) (w : List (Fin n × Bool)) :
    FreeGroup.lift f (FreeGroup.mk w) = KB.sword gen (w.map fun l => (l.1.val, l.2)) := by
  rw [FreeGroup.lift_mk, KB.sword, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ⟨i, b⟩ _
  cases b <;> simp [hf]

theorem rt_get (r : ℕ) (hr : r < 12) :
    wList (wW (KRS.RT r)) (wN (KRS.RT r)) = (rels[r]'(by simpa [rels] using hr)).map tcode := by
  have h := congrArg (fun L => L[r]?) rt_bind
  simp only [List.getElem?_map, List.getElem?_range hr, Option.map_some] at h
  rw [List.getElem?_eq_getElem (by simpa [rels] using hr), Option.map_some, Option.some.injEq] at h
  exact h

theorem rels_lt (r : ℕ) (hr : r < 12) : ∀ p ∈ rels[r]'(by simpa [rels] using hr), p.1 < 3 := by
  have h : rels.all (fun w => w.all fun p => decide (p.1 < 3)) = true := by decide
  intro p hp
  have := List.all_eq_true.mp (List.all_eq_true.mp h _ (List.getElem_mem _)) p hp
  simpa using this

theorem wval_rt {G : Type*} [Group G] (x y t : G) (ht : t⁻¹ = t) (r : ℕ) (hr : r < 12) :
    wval (lets x y t) (wW (KRS.RT r)) (wN (KRS.RT r)) =
      KB.sword (fun g => if g = 0 then x else if g = 1 then y else t) (rels[r]'(by simpa [rels] using hr)) := by
  rw [wval_eq, rt_get r hr, prod_tcode x y t ht _ (rels_lt r hr)]

theorem m24_rels : CFSG.KBAlt.M24.rels = rels.take 7 := by decide

theorem j4_hN : ∀ (H : Type) [Group H] (a b : H),
    (∀ r < 12, nOnly (wW (CFSG.KJ4.RUN.kd.RT r)) (wN (CFSG.KJ4.RUN.kd.RT r)) →
      wval (lets a b 1) (wW (CFSG.KJ4.RUN.kd.RT r)) (wN (CFSG.KJ4.RUN.kd.RT r)) = 1) →
    Finite (Subgroup.closure {a, b}) ∧ Nat.card (Subgroup.closure {a, b}) ≤ CFSG.KJ4.RUN.kd.BN := by
  intro H _ a b hrel
  change ∀ r < 12, nOnly (wW (KRS.RT r)) (wN (KRS.RT r)) →
    wval (lets a b 1) (wW (KRS.RT r)) (wN (KRS.RT r)) = 1 at hrel
  set P := TauCeti.Sporadic.m24Presentation
  let gen : ℕ → H := fun g => if g = 0 then a else if g = 1 then b else 1
  have hval : ∀ w ∈ P.relatorLetters, KB.sword gen w = 1 := by
    intro w hw
    rw [CFSG.KBAlt.M24.rels_eq, m24_rels] at hw
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hw
    have hr7 : r < 7 := by simpa [rels] using hr
    have h1 := hrel r (by omega) (rt_nOnly r hr7)
    rw [wval_rt a b 1 inv_one r (by omega)] at h1
    rw [List.getElem_take]
    exact h1
  let f : Fin P.generatorCount → H := fun i => gen i.val
  have hf : ∀ r ∈ P.relatorSet, FreeGroup.lift f r = 1 := by
    intro r hr
    rw [CFSG.Sporadic.Presentation.relatorSet_eq] at hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [lift_mk_sword gen f (fun _ => rfl)]
    apply hval
    rw [TauCeti.GroupPresentation.relatorLetters_def]
    exact List.mem_map_of_mem hw
  let φ : P.Group →* H := PresentedGroup.toGroup hf
  have hrange : φ.range = Subgroup.closure {a, b} := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 1
    ext z
    simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hn : P.generatorCount = 2 := m24_gens
    constructor
    · rintro ⟨i, rfl⟩
      rw [PresentedGroup.toGroup.of]
      have hi : i.val < 2 := hn ▸ i.isLt
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
      · left
        simp [f, gen, h]
      · right
        simp [f, gen, h]
    · rintro (rfl | rfl)
      · refine ⟨⟨0, by omega⟩, ?_⟩
        rw [PresentedGroup.toGroup.of]
        simp [f, gen]
      · refine ⟨⟨1, by omega⟩, ?_⟩
        rw [PresentedGroup.toGroup.of]
        simp [f, gen]
  obtain ⟨hfin, hcard⟩ := m24
  have hfin' : Finite P.Group := hfin
  rw [← hrange]
  refine ⟨Finite.of_surjective _ φ.rangeRestrict_surjective, ?_⟩
  calc Nat.card φ.range ≤ Nat.card P.Group := Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
    _ ≤ 244823040 := hcard
    _ = CFSG.KJ4.RUN.kd.BN := (Nat.beq_eq.mp (by quickRfl)).symm

theorem j4_gens : TauCeti.Sporadic.j4Presentation.generatorCount = 3 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.j4Presentation_generatorNames]

theorem j4 : Finite TauCeti.SporadicName.J4.Group ∧
    Nat.card TauCeti.SporadicName.J4.Group ≤ 86775571046077562880 := by
  change Finite TauCeti.Sporadic.j4Presentation.Group ∧
    Nat.card TauCeti.Sporadic.j4Presentation.Group ≤ 86775571046077562880
  set P := TauCeti.Sporadic.j4Presentation
  have hrel : ∀ w ∈ rels, KB.sword (KB.tcGen P) w = 1 := by
    intro w hw
    rw [← rels_eq] at hw
    exact KB.sword_relatorLetters P w hw
  have ht : (KB.tcGen P 2)⁻¹ = KB.tcGen P 2 := by
    have h7 := hrel (rels[7]) (List.getElem_mem _)
    simp only [rels, List.getElem_cons_succ, List.getElem_cons_zero, KB.sword, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, ite_true, mul_one] at h7
    exact inv_eq_of_mul_eq_one_right h7
  have hR : ∀ r < 12, wval (lets (KB.tcGen P 0) (KB.tcGen P 1) (KB.tcGen P 2)) (wW (CFSG.KJ4.RUN.kd.RT r))
      (wN (CFSG.KJ4.RUN.kd.RT r)) = 1 := by
    intro r hr
    change wval _ (wW (KRS.RT r)) (wN (KRS.RT r)) = 1
    rw [wval_rt _ _ _ ht r hr]
    have hw := hrel _ (List.getElem_mem (by simpa [rels] using hr))
    have hlt := rels_lt r hr
    rw [← hw, KB.sword, KB.sword]
    congr 1
    apply List.map_congr_left
    intro p hp
    have hp3 := hlt p hp
    obtain ⟨g, b⟩ := p
    rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl <;> simp
  obtain ⟨hfin, hcard⟩ := j4Ok_sound' j4_ok fix_ok pts_ok mfix_ok J4KShape.wrec_len (by decide +kernel) j4_hN _ _ _ (mul_eq_one_iff_inv_eq.mpr ht) hR
  have htop : Subgroup.closure {KB.tcGen P 0, KB.tcGen P 1, KB.tcGen P 2} = ⊤ := by
    have hn : P.generatorCount = 3 := j4_gens
    rw [← KB.closure_tcGen P]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_ofPred_eq, hn]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl <;> simp
  rw [htop] at hfin hcard
  refine ⟨Finite.of_equiv _ Subgroup.topEquiv.toEquiv, ?_⟩
  rw [← Subgroup.card_top]
  calc Nat.card (⊤ : Subgroup P.Group) ≤ _ := hcard
    _ = 86775571046077562880 := Nat.beq_eq.mp (by quickRfl)

end CertificateChecks.KernelBounds

end
