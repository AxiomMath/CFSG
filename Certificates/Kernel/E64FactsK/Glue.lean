module

public import Certificates.Kernel.E64FactsK.Checks
public import Certificates.Kernel.E64Aut.Glue
public import CFSG.Certificates.Kernel.E64FactsKSound

public section

namespace CFSG.KD.E64FactsK

open CFSG.KC.WrTwin CFSG.KC.E64AutK CFSG.KC.E64FactsK CFSG.KD.E64Aut
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.E64Data Certificates.AE117 Certificates.E64Aut Certificates.E64Facts

theorem finAll_iff_k {α : Type} {s : Finset α} {f : α → Bool} :
    finAll s f = true ↔ ∀ x ∈ s, f x = true := by
  unfold finAll
  exact decide_eq_true_iff

theorem centOK_k {ℓ : Finset (Fin 7)} (hℓ : ℓ ∈ fanoLines) :
    Certificates.E64Facts.centOK (l32Fin ()) (evenFin ()) (memS ℓ) (centAt ℓ) = true := by
  have hA := List.all_eq_true.1 e64f_g1 ℓ hℓ
  simp only [Bool.and_eq_true] at hA
  have h2 := List.all_eq_true.1 e64f_cent ℓ hℓ
  rw [memS_eq, centAt_eq]
  unfold Certificates.E64Facts.centOK
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true] at hA ⊢
    intro c hc
    have h3 := hA.1.1.1.1 c hc
    rwa [commP_eq (pp := pi14) rfl] at h3
  · rw [finAll_iff_k]
    intro τ hτ
    by_cases hS : ((memSK ℓ).all fun s => decide (τ * s.perm = s.perm * τ)) = true
    · rw [hS, Bool.not_true, Bool.false_or, finAll_iff_k]
      intro v hv
      by_cases hc : commAll (memSK ℓ) ⟨v, τ⟩ = true
      · rw [hc, Bool.not_true, Bool.false_or]
        obtain ⟨c, hc', he⟩ := centCOK_sound rfl h2 ⟨v, τ⟩ (mem_P168 hτ) (mem_V64 hv)
          (fun s hs => List.all_eq_true.1 hc s hs)
        exact List.any_eq_true.2 ⟨c, hc', he⟩
      · rw [Bool.not_eq_true] at hc
        rw [hc, Bool.not_false, Bool.true_or]
    · rw [Bool.not_eq_true] at hS
      rw [hS, Bool.not_false, Bool.true_or]

theorem g1Check_k : g1Check () = true := by
  unfold g1Check
  rw [List.all_eq_true]
  intro ℓ hℓ
  have hA := List.all_eq_true.1 e64f_g1 ℓ hℓ
  simp only [Bool.and_eq_true] at hA ⊢
  obtain ⟨⟨⟨⟨-, hB⟩, hC⟩, hD⟩, hE⟩ := hA
  refine ⟨⟨⟨⟨centOK_k hℓ, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [centAt_eq]
    exact hB
  · rw [centAt_eq, distinctPi_eq rfl]
    exact hC
  · rw [centAt_eq, all_sq_eq rfl]
    exact hD
  · rw [centAt_eq, all_comm_eq]
    exact hE

theorem g2Check_k : g2Check () = true := by
  have h := e64f_g2
  simp only [Bool.and_eq_true, e14, pi14] at h
  obtain ⟨⟨hA, hB⟩, hC⟩ := h
  unfold g2Check
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [centAt_eq, memS_eq, ← commP_eq rfl, ← any_eqPi_eq rfl, ← eqPi_eq rfl]
    simpa only [List.all_map, Function.comp_def] using hA
  · rw [distinctPi_eq rfl]
    exact hB
  · simp only [memS_eq, ← commP_eq rfl, ← eqPi_eq rfl, ← beq_enc, ← pm_enc]
    exact hC

theorem conjCheck_k : conjCheck () = true := e64f_conj

end CFSG.KD.E64FactsK

end
