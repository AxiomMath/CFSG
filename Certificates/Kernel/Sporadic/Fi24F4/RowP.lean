module

public import Certificates.Kernel.Sporadic.Fi24F4.RowPC
public import Certificates.Kernel.Sporadic.Fi24F4.RowK
public import CFSG.Certificates.Kernel.Spor.Fi24F4Class

public section

namespace CertificateChecks.KernelSpor.Fi24F4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.Fi24F4 CFSG.KS.Fi24F4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Fi24I301 CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi24C
open CFSG.KS.Raw.Orb (PRep)

noncomputable abbrev pGen (l : ℕ) : Equiv.Perm (Fin 378) := if l = 0 then fi24Pa else fi24Pb

theorem pGen_prep {l : ℕ} (hl : l < 2) :
    PRep 378 9 (Fi24PC.S l) (pGen l) ∧ PRep 378 9 (Fi24PC.SI l) (pGen l)⁻¹ := by
  interval_cases l
  · simp only [pGen, if_true]
    rw [fi24Pa_eq]
    exact prep_gen (permP' (by norm_num))
  · simp only [pGen, one_ne_zero, if_false]
    rw [fi24Pb_eq]
    exact prep_gen (permP' (by norm_num))

theorem fi24P_gen : fi24P = Subgroup.closure (pGen '' {l | l < 2}) := by
  rw [@fi24P_eq]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by simp [pGen]⟩
    · exact ⟨1, by norm_num, by simp [pGen]⟩
  · rintro ⟨l, hl, rfl⟩
    interval_cases l
    · left
      simp [pGen]
    · right
      simp [pGen]

theorem prep_PY0 : PRep 378 9 (Fi24PY.T 0) (CFSG.Sporadic.Th.wordG pLet dWord ^ 4) ∧
    canonK 378 9 (mask 9) (378 * 9) (Fi24PY.T 0) = true := by
  rw [← wordG_dWord4]
  exact prep_pWord (by decide) Fi24PY.yRec

theorem card_P_centralizer :
    Nat.card ↥(fi24P ⊓ Subgroup.centralizer
      ({CFSG.Sporadic.Th.wordG pLet dWord ^ 4} : Set (Equiv.Perm (Fin 378)))) = 5832 := by
  have hS := steps_of (N := 3359) (NS := 53) (CH := 64) (by norm_num) Fi24PY.hS
  have hA := acts_of (n := 378) (w := 9) (r := 2) (wp := 12) (m := 3360) (NS := 53) (CH := 64)
    (by norm_num) Fi24PY.hA
  have hD := dists_of (m := 3360) (NS := 53) (CH := 64) (by norm_num) Fi24PY.hD
  have h0 := prep_PY0
  have hc0 : Fi24PY.T 0 >>> (378 * 9) = 0 := (CFSG.KS.PF.canon_facts h0.2).2.2.1
  have h := card_eq_mul_of_tree (m := 3360) (by norm_num) (by norm_num) fi24P fi24P_gen
    (fun l hl => pGen_prep hl) h0.1 hc0 (by norm_num) (fun i hi => hS i (by omega)) (by norm_num)
    hA hD
  rw [@card_fi24P] at h
  omega

end CertificateChecks.KernelSpor.Fi24F4

end
