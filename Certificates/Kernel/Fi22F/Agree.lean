module

public import Certificates.Kernel.Fi22F.Pairs
public import CFSG.Sporadic.Presentation.Fi22ExactWalksInputs
public import CFSG.Certificates.CentralizerWalks
public import CFSG.Certificates.CosetTableAction
import CFSG.Sporadic.Presentation.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelFi22F

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.LCE CFSG.Certificates.CosetEnumeration
  CFSG.Sporadic.Presentation.Fi22Exact CertificateChecks.KernelCo2 CertificateChecks.KernelFi22

theorem presLetter_eq_letV {m : ℕ} (rels : Set (FreeGroup (Fin m))) {c : ℕ} (hc : c < 2 * m)
    (h255 : c ≠ 255) : presLetter rels c = letV (pgen rels) c := by
  obtain ⟨i, rfl | rfl⟩ : ∃ i, c = 2 * i ∨ c = 2 * i + 1 := ⟨c / 2, by omega⟩
  · have hi : i < m := by omega
    have h := presLetter_even rels ⟨i, hi⟩
    rw [h, letV, if_neg h255, if_pos (by omega), show 2 * i / 2 = i by omega, pgen_lt rels hi]
  · have hi : i < m := by omega
    have h := presLetter_odd rels ⟨i, hi⟩
    rw [h, letV, if_neg h255, if_neg (by omega), show (2 * i + 1) / 2 = i by omega,
      pgen_lt rels hi]

theorem gW_lt (n : ℕ) (c : List (Fin 6)) : ∀ y ∈ gW n c, y < 4 := by
  intro y hy
  simp only [gW, xW, List.mem_append, List.mem_replicate, List.mem_flatMap, List.mem_cons] at hy
  omega

theorem agree_of_cent {m : ℕ} (hm : 2 ≤ m) (rels : Set (FreeGroup (Fin m))) {pp : Conj × Conj}
    (h : ((pairWord pp).map (letV (pgen rels))).prod ∈ Subgroup.centralizer {pgen rels 0}) :
    (evalWord (presLetter rels) (gW pp.1.1 pp.1.2))⁻¹ * presLetter rels 0 *
        evalWord (presLetter rels) (gW pp.1.1 pp.1.2) =
      (evalWord (presLetter rels) (gW pp.2.1 pp.2.2))⁻¹ * presLetter rels 0 *
        evalWord (presLetter rels) (gW pp.2.1 pp.2.2) := by
  have hw2 : ∀ c ∈ gW pp.2.1 pp.2.2, c < 2 * m := fun c hc => by
    have := gW_lt _ _ c hc
    omega
  have hl : ∀ c ∈ pairWord pp, c < 4 := by
    intro c hc
    simp only [pairWord, List.mem_append] at hc
    rcases hc with hc | hc
    · exact gW_lt _ _ c hc
    · simp only [invC, List.mem_map, List.mem_reverse] at hc
      obtain ⟨d, hd, rfl⟩ := hc
      have := gW_lt _ _ d hd
      simp only [invCode]
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;> decide
  have he : ((pairWord pp).map (letV (pgen rels))).prod = evalWord (presLetter rels) (pairWord pp) := by
    unfold evalWord
    congr 1
    apply List.map_congr_left
    intro c hc
    have := hl c hc
    exact (presLetter_eq_letV rels (by omega) (by omega)).symm
  have h0 : pgen rels 0 = presLetter rels 0 := by
    rw [presLetter_eq_letV rels (by omega) (by omega)]
    rfl
  rw [he, h0, Subgroup.mem_centralizer_singleton_iff, pairWord, evalWord_append',
    evalWord_invC hw2] at h
  exact conj_eq_of_commute_mul_inv _ _ _ h.symm

theorem pairs_agree : ∀ pp ∈ allPairs,
    (evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk})
        (gW pp.1.1 pp.1.2))⁻¹ *
      presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk} 0 *
      evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk}) (gW pp.1.1 pp.1.2) =
    (evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk})
        (gW pp.2.1 pp.2.2))⁻¹ *
      presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk} 0 *
      evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk}) (gW pp.2.1 pp.2.2) := by
  intro pp hpp
  have key : ∀ T : Set (FreeGroup (Fin P.generatorCount)), P.relatorSet = T →
      (evalWord (presLetter T) (gW pp.1.1 pp.1.2))⁻¹ * presLetter T 0 *
          evalWord (presLetter T) (gW pp.1.1 pp.1.2) =
        (evalWord (presLetter T) (gW pp.2.1 pp.2.2))⁻¹ * presLetter T 0 *
          evalWord (presLetter T) (gW pp.2.1 pp.2.2) := by
    intro T hT
    subst hT
    exact agree_of_cent (by rw [gens_eq]) _ (pairs_cent pp hpp)
  exact key {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk}
    (CFSG.Sporadic.Presentation.relatorSet_eq P)

theorem codes_W0 : codes W0 =
    CFSG.KD.OrdFi22.rels.map (List.map fun l => 2 * l.1 + if l.2 then 0 else 1) := by
  have h := CFSG.KD.OrdFi22.rels_eq
  rw [TauCeti.GroupPresentation.relatorLetters_def] at h
  change codes TauCeti.Sporadic.fi22Presentation.relators = _
  rw [← h, List.map_map]
  unfold codes
  apply List.map_congr_left
  intro w _
  rw [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  rintro ⟨i, b⟩ _
  cases b <;> simp [letterCode]

theorem rel_a2_mem : [0, 0] ∈ codes W0 := by
  rw [codes_W0]
  decide +kernel

theorem rel_b13_mem : List.replicate 13 2 ∈ codes W0 := by
  rw [codes_W0]
  decide +kernel

theorem rel_ab11_mem : (List.replicate 11 [0, 2]).flatten ∈ codes W0 := by
  rw [codes_W0]
  decide +kernel

theorem rel_ab2_21_mem : (List.replicate 21 [0, 2, 2]).flatten ∈ codes W0 := by
  rw [codes_W0]
  decide +kernel

theorem len_g2 : g2w.length = 2520 := by decide +kernel

end CertificateChecks.KernelFi22F

end
