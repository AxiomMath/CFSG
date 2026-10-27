module

public import Certificates.Data.CFSGNative.Recognition.HSPinnedData
public import Mathlib.Data.Fintype.Card
public import CFSG.Sporadic.Recognition.HSGraphModel
public import Certificates.Certificate6102
import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsInputs
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
meta import CFSG.Monster.B.Classical.PlaneData
import CFSG.Sporadic.Recognition.HSGraphModelInputs
import Certificates.Certificate6102
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CertificateChecks.KernelHSPinned6101

open CFSG.Sporadic.Recognition.HSGraph CFSG.ComponentClassification.WittDesign
  CFSG.Sporadic.Recognition.HSPinned CFSG.Sporadic.Recognition.HSPinned.Native

private noncomputable def phi : Fin 100 ≃ Vert hexads :=
  (Equiv.ofBijective isoFun (Finite.injective_iff_bijective.1 fun i j h =>
    Certificates.certificate6102.1 i j h)).trans modelVertEquiv

private theorem phi_apply (k : Fin 100) : phi k = modelVertAtF (isoFun k) := rfl

private theorem phi_adj (i j : Fin 100) : adjB i j = true ↔ (hsGraph hexads).Adj (phi i) (phi j) := by
  rw [phi_apply, phi_apply]
  exact Certificates.certificate6102.2 i j

theorem srg_deg : ∀ v : Fin 100,
    (Finset.univ.filter fun w : Fin 100 => adjB v w = true).card = 22 := by
  intro v
  rw [← degree_hexads (phi v), ← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_equiv phi fun w => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset,
      phi_adj]

theorem srg_lam : ∀ v w : Fin 100, adjB v w = true →
    (Finset.univ.filter fun z : Fin 100 => adjB v z = true ∧ adjB w z = true).card = 0 := by
  intro v w h
  have hc := commonNeighbors_adj_hexads (phi v) (phi w) ((phi_adj v w).1 h)
  rw [← Set.toFinset_card] at hc
  rw [← hc]
  exact Finset.card_equiv phi fun z => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      SimpleGraph.mem_commonNeighbors, phi_adj]

theorem srg_mu : ∀ v w : Fin 100, v ≠ w → adjB v w = false →
    (Finset.univ.filter fun z : Fin 100 => adjB v z = true ∧ adjB w z = true).card = 6 := by
  intro v w hne h
  have hc := commonNeighbors_not_adj_hexads (phi v) (phi w) (phi.injective.ne hne)
    (by rw [← phi_adj, h]; decide)
  rw [← Set.toFinset_card] at hc
  rw [← hc]
  exact Finset.card_equiv phi fun z => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      SimpleGraph.mem_commonNeighbors, phi_adj]

theorem nbr_exists : ∀ x < 100, ∃ y < 100, adjB x y = true := by
  intro x hx
  obtain ⟨w, hw⟩ := Finset.card_pos.1 (by rw [srg_deg ⟨x, hx⟩]; norm_num)
  exact ⟨w.val, w.isLt, (Finset.mem_filter.1 hw).2⟩

theorem card_non_nbrs :
    (Finset.univ.filter fun w : Fin 100 => w ≠ 0 ∧ adjB 0 w = false).card = 77 := by
  have h0 : adjB 0 0 = false := by
    cases h : adjB 0 0
    · rfl
    · exact absurd ((phi_adj 0 0).1 h) ((hsGraph hexads).irrefl)
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun w : Fin 100 => adjB 0 w = true)
  have hA : (Finset.univ.filter fun w : Fin 100 => adjB 0 w = true).card = 22 := srg_deg 0
  rw [hA, Finset.card_univ, Fintype.card_fin] at hsum
  have hB : (Finset.univ.filter fun w : Fin 100 => w ≠ 0 ∧ adjB 0 w = false) =
      (Finset.univ.filter fun w : Fin 100 => ¬ adjB 0 w = true).erase 0 := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Bool.not_eq_true]
  rw [hB, Finset.card_erase_of_mem (by simpa using h0)]
  omega

end CertificateChecks.KernelHSPinned6101

end
