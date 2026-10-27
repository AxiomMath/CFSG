
module

public import Certificates.Kernel.LocalComp.M22TriplesCheck
public import CFSG.Certificates.Kernel.TripleOrbitSound
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22TransitiveBase

public section

namespace CertificateChecks.KernelLC

open Equiv MulAction CFSG.ComponentClassification.WittDesign CFSG.KLie.CT

@[expose] def permA : Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

@[expose] def permB : Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem m22_eq : CFSG.Blueprint.NativeSporadic.M22 = Subgroup.closure {permA, permB} := rfl

theorem permA_tab : ∀ x : Fin 22, (permA x).val = fget M22Tr.G0 x.val 5 := by
  intro x
  fin_cases x <;> rfl

theorem permB_tab : ∀ x : Fin 22, (permB x).val = fget M22Tr.G1 x.val 5 := by
  intro x
  fin_cases x <;> rfl

theorem exists_smul_baseTriple (e : Fin 3 ↪ Fin 22) : ∃ g : M22, g • baseTriple = e := by
  obtain ⟨g, hg, he⟩ := CFSG.KC.Triple.tripleOrbit_sound permA_tab permB_tab M22Tr.ok e
  have hg' : g ∈ CFSG.Blueprint.NativeSporadic.M22 := by
    rw [m22_eq]
    exact hg
  refine ⟨⟨g, hg'⟩, ?_⟩
  ext i
  exact congrArg Fin.val (he i)

theorem card_stabilizer_baseTriple' :
    Nat.card (stabilizer M22 baseTriple) = 48 := by
  have h : Nat.card (orbit M22 baseTriple) * Nat.card (stabilizer M22 baseTriple) = 443520 :=
    card_orbit_mul_card_stabilizer baseTriple
  have horb : orbit M22 baseTriple = Set.univ :=
    Set.eq_univ_of_forall fun e => mem_orbit_iff.2 (exists_smul_baseTriple e)
  rw [horb, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin] at h
  have h3 : Nat.descFactorial 22 3 = 9240 := rfl
  rw [h3] at h
  omega

theorem m22Count_triple :
    m22Count (fun g => g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2) = 48 := by
  rw [← card_m22_subtype, ← card_stabilizer_baseTriple']
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_baseTriple_iff.symm)

end CertificateChecks.KernelLC

end
