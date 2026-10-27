
module

public import Certificates.Kernel.L34Pk.Pk
public import Certificates.Kernel.L34Pk.Checks

public section

namespace CertificateChecks.KernelL34

open Equiv CFSG.KS.PCnt CFSG.KC.L34 CFSG.KC.WCnt CFSG.Quasithin.L34Amalgam
  CFSG.Quasithin.Asc94 CFSG.ComponentClassification.WittDesign

theorem extra_three (i : Fin 12) : extra i 3 = (letter 's' :: word (repStr i)) ++
    (letter 's' :: word (repStr i)) ++ (letter 's' :: word (repStr i)) := by
  have hs : ("s" : String).toList = ['s'] := by decide +kernel
  unfold extra word
  rw [String.toList_join]
  simp only [List.replicate, List.flatMap_cons, List.flatMap_nil, String.toList_append, hs,
    List.map_append, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
    List.nil_append, List.append_assoc]

theorem gen_facts : ∀ j : Fin 5, j.val < 3 → upk22 (gL.getD j.val 0) 0 = 0 ∧
    upk22 (gL.getD j.val 0) 1 = 1 ∧ ∀ p ∈ m22HexadL, upk22 (gL.getD j.val 0) p ∈ m22HexadL := by
  decide +kernel

theorem t_facts : upk22 (gL.getD 3 0) 0 = 0 ∧ upk22 (gL.getD 3 0) 1 = 1 ∧
    ¬ (∀ p ∈ m22HexadL, upk22 (gL.getD 3 0) p ∈ m22HexadL) ∧
    upk22 (gL.getD 4 0) 0 = 0 ∧ upk22 (gL.getD 4 0) 1 ≠ 1 ∧
    (∀ p ∈ m22HexadL, upk22 (gL.getD 4 0) p ∈ m22HexadL) := by
  decide +kernel

theorem sq_eq_one {g : M22} {G : Nat} (hg : pkw 5 (g : Perm (Fin 22)) = G)
    (h : Nat.beq (pm G G) pI = true) : g * g = 1 :=
  Subtype.ext (pkw_inj (n := 22) (w := 5) (by norm_num) (by
    rw [Subgroup.coe_mul, pkw_mul', hg, OneMemClass.coe_one, pk_one']
    exact Nat.eq_of_beq_eq_true h))

theorem facts7036 :
    (∀ j : Fin 5, j.val < 3 → (gen j : Equiv.Perm (Fin 22)) 0 = 0 ∧
       (gen j : Equiv.Perm (Fin 22)) 1 = 1 ∧
       ∀ p ∈ m22HexadL, (gen j : Equiv.Perm (Fin 22)) p ∈ m22HexadL)
    ∧ ((bT1 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (bT1 : Equiv.Perm (Fin 22)) 1 = 1 ∧
       ¬ (∀ p ∈ m22HexadL, (bT1 : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧ bT1 * bT1 = 1 ∧
       (bT2 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (bT2 : Equiv.Perm (Fin 22)) 1 ≠ 1 ∧
       (∀ p ∈ m22HexadL, (bT2 : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧ bT2 * bT2 = 1)
    ∧ (∀ w ∈ amalRels, evalW gen w = 1)
    ∧ (∀ i : Fin 12, IsGood i → evalW gen (extra i 3) = 1) := by
  refine ⟨fun j hj => ?_, ?_, fun w hw => ?_, fun i hi => ?_⟩
  · rw [coe_eq_upk (pk_gen j)]
    exact gen_facts j hj
  · obtain ⟨a0, a1, a2, b0, b1, b2⟩ := t_facts
    rw [coe_eq_upk pk_t1, coe_eq_upk pk_t2]
    exact ⟨a0, a1, a2, sq_eq_one pk_t1 (by decide +kernel), b0, b1, b2,
      sq_eq_one pk_t2 (by decide +kernel)⟩
  · exact evalW_gen_eq_one (List.all_eq_true.1 k_amal w hw)
  · have h := List.all_eq_true.1 k_extra i (List.mem_finRange i)
    rw [decide_eq_true hi, Bool.not_true, Bool.false_or] at h
    rw [extra_three]
    exact evalW_gen_eq_one h

end CertificateChecks.KernelL34

end
