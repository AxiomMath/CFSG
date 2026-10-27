module

public import Certificates.Kernel.L34Pk.Pk
public import Certificates.Kernel.L34Pk.Checks

public section

namespace CertificateChecks.KernelL34

open Equiv CFSG.KS.PCnt CFSG.KC.L34 CFSG.Quasithin.L34Amalgam
  CFSG.ComponentClassification.WittDesign

theorem pk_crd (x : Fin 16) : pkw 5 ((crd x : M22) : Perm (Fin 22)) = cL.getD x.val 0 := by
  unfold crd
  simp only [Subgroup.coe_mul, pkw_mul', pk_selM]
  rw [pk_e0, pk_e1, pk_e2, pk_e3]
  exact k_crd x

theorem genTL_enc : genTL.map encT = gL := by
  simp only [genTL, List.map_cons, List.map_nil, encT_tab, pk_c1, pk_c2, pk_c3, pk_t1, pk_t2]
  rfl

theorem genTiL_enc : genTiL.map encT = giL := by
  simp only [genTiL, List.map_cons, List.map_nil, encT_tab, pk_c1i, pk_c2i, pk_c3i, pk_t1i,
    pk_t2i]
  rfl

theorem crdTL_enc : crdTL.map encT = cL := by
  unfold crdTL
  rw [List.map_map]
  have e : (encT ∘ fun x : Fin 16 => tab (crd x)) = fun x : Fin 16 => cL.getD x.val 0 := by
    funext x
    rw [Function.comp_apply, encT_tab, pk_crd]
  rw [e]
  decide +kernel

theorem V_genTL : ∀ T ∈ genTL, V T := by
  intro T hT
  simp only [genTL, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl <;> exact V_tab _

theorem V_genTiL : ∀ T ∈ genTiL, V T := by
  intro T hT
  simp only [genTiL, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl <;> exact V_tab _

theorem V_crdTL : ∀ T ∈ crdTL, V T := by
  intro T hT
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hT
  exact V_tab _

theorem facts7079 :
    (a2Check genTL genTiL = true)
    ∧ (pqCheck genTL genTiL crdTL = true)
    ∧ (invCheck genTL genTiL crdTL = true)
    ∧ (conjCheck genTL genTiL = true)
    ∧ (s1Check genTL genTiL = true)
    ∧ (rhCheck genTL genTiL = true)
    ∧ (glueCheck genTL genTiL crdTL = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a2Check_eq, genTL_enc, genTiL_enc]
    exact k_a2
  · rw [pqCheck_eq V_crdTL V_genTL, genTL_enc, genTiL_enc, crdTL_enc]
    exact k_pq
  · rw [invCheck_eq V_crdTL, genTL_enc, genTiL_enc, crdTL_enc]
    exact k_inv
  · rw [conjCheck_eq V_genTL V_genTiL, genTL_enc, genTiL_enc]
    exact k_conj
  · rw [s1Check_eq, genTL_enc, genTiL_enc]
    exact k_s1
  · rw [rhCheck_eq V_genTL, genTL_enc, genTiL_enc]
    exact k_rh
  · rw [glueCheck_eq V_crdTL V_genTL, genTL_enc, genTiL_enc, crdTL_enc]
    exact k_glue

end CertificateChecks.KernelL34

end
