module

public import Certificates.Kernel.WrTwin.E29Checks
public import Certificates.Kernel.WrTwin.E29RowsA
public import Certificates.Kernel.WrTwin.E29RowsB
public import CFSG.Certificates.Kernel.WrTwinSound
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.KD.WrTwin

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3.E29Data CFSG.ClassicalInvolution.Q3.AE

theorem e29_rows_hold : ∀ d ∈ e29ConjData,
    nG d.1 * nG (2 * d.2.1 + d.2.2.1) * (nG d.1)⁻¹ = nWord d.2.2.2.1 d.2.2.2.2 ∨
      nG d.1 * nG (2 * d.2.1 + d.2.2.1) * (nG d.1)⁻¹ = nWord d.2.2.2.1 d.2.2.2.2 * Wr.allOnes 8 := by
  intro d hd
  obtain ⟨hT, hTi⟩ := tabOK_sound e29_tab
  have hr : rowPiOK 16 id16 pi8 56 g29 i29 d = true := by
    rw [← List.take_append_drop 1568 e29ConjData, List.mem_append] at hd
    rcases hd with hd | hd
    · exact List.all_eq_true.mp e29_rowsA d hd
    · exact List.all_eq_true.mp e29_rowsB d hd
  exact rowPiOK_sound (n := 8) (by norm_num) e29_id e29_pi hT hTi hr

theorem le_card_aglFin : 1344 ≤ (aglFin ()).card := by
  have hS : ∀ g ∈ agl32 ⊓ alternatingGroup (Fin 8), g ∈ aglFin () := by
    intro g hg
    rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup] at hg
    have h1 : ∀ s ∈ affinePlanes, s.map g.toEmbedding ∈ affinePlanes ∧
        s.map g⁻¹.toEmbedding ∈ affinePlanes := hg.1
    simp only [aglFin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, hg.2⟩
  have hmem : ∀ σ, mem29 σ = true → σ ∈ agl32 ⊓ alternatingGroup (Fin 8) := by
    intro σ h
    have h' := of_decide_eq_true h
    rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup]
    exact ⟨h'.1, h'.2⟩
  have := le_card_of_chainOK _ _ hS hmem _ _ e29_chain
  rwa [e29_chain_len] at this

end CFSG.KD.WrTwin

end
