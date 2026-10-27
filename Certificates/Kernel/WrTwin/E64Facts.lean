module

public import Certificates.Kernel.WrTwin.E64Checks
public import CFSG.Certificates.Kernel.WrTwinSound
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.KD.WrTwin

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3.E64Data CFSG.ClassicalInvolution.Q3.AE

theorem e64_rows_hold : ∀ d ∈ e64ConjData,
    mG d.1 * mG (2 * d.2.1 + d.2.2.1) * (mG d.1)⁻¹ = mWord d.2.2.2.1 d.2.2.2.2 := by
  intro d hd
  obtain ⟨hT, hTi⟩ := tabOK_sound e64_tab
  exact rowOK_sound (n := 7) (by norm_num) e64_id hT hTi (List.all_eq_true.mp e64_rows d hd)

theorem le_card_l32Fin : 168 ≤ (l32Fin ()).card := by
  have hS : ∀ g ∈ l32 ⊓ alternatingGroup (Fin 7), g ∈ l32Fin () := by
    intro g hg
    rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup] at hg
    have h1 : ∀ s ∈ fanoLines, s.map g.toEmbedding ∈ fanoLines ∧ s.map g⁻¹.toEmbedding ∈ fanoLines :=
      hg.1
    simp only [l32Fin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, hg.2⟩
  have hmem : ∀ σ, mem64 σ = true → σ ∈ l32 ⊓ alternatingGroup (Fin 7) := by
    intro σ h
    have h' := of_decide_eq_true h
    rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup]
    exact ⟨h'.1, h'.2⟩
  have := le_card_of_chainOK _ _ hS hmem _ _ e64_chain
  rwa [e64_chain_len] at this

end CFSG.KD.WrTwin

end
