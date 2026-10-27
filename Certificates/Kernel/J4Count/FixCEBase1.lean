
module

public import Certificates.Kernel.J4Count.FixCEBase

public import Certificates.Kernel.J4Count.FixCEEltBase1

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 (toVecD)
open CFSG.Sporadic.GLQ CFSG.KC.J4FixCE CFSG.KD.J4FixCE
open CFSG.KC.J4FixC (nth codeL toI walkK letM sN)
open CFSG.KC.J4Q (vecJ mulJ)
open CFSG.KD.J4Q (c rm one A B Bi)
open CertificateChecks.KernelSporSch CertificateChecks.KernelJ4Count
open CFSG.Quasithin.J4M2 (cE)

section Sizes

end Sizes

section Fix

end Fix

section Points

theorem pt_fixed {i : ℕ} (hi : i < 737) : cE • ptR i = ptR i :=
  fix_of_PR PR_cE (pt_lt hi) (pt_spec hi).2

section W77

theorem letter_inv_smul_ab (k s : ℕ) :
    (letter a b (codeL k))⁻¹ • toRow (toVecD 112 s) =
      toRow (toVecD 112 (vecJ rm s (letM A A B Bi k))) := by
  have ha := rep_a matFacts
  have hb := rep_b matFacts
  rw [letM_eq']
  rcases k with _ | _ | _ | k
  · have e : letter a b (codeL 0) = a := by simp [letter, codeL]
    rw [e, inv_smul_toRow ha]
    change toRow (toVecD 112 (CFSG.Sporadic.SmallF2.Native.vecMulN 112 An.1 s)) = _
    rw [CFSG.KS.SporSch.J4B.vec_enc J4Real.hK J4InvP.pA.1.1, J4InvP.pA.1.2]
    rfl
  · have e : letter a b (codeL 1) = a⁻¹ := by simp [letter, codeL]
    rw [e, inv_smul_toRow (rep_invP ha)]
    change toRow (toVecD 112 (CFSG.Sporadic.SmallF2.Native.vecMulN 112 An.2 s)) = _
    rw [CFSG.KS.SporSch.J4B.vec_enc J4Real.hK J4InvP.pA.2.1, J4InvP.pA.2.2]
    rfl
  · have e : letter a b (codeL 2) = b := by simp [letter, codeL]
    rw [e, inv_smul_toRow hb]
    change toRow (toVecD 112 (CFSG.Sporadic.SmallF2.Native.vecMulN 112 Bn.1 s)) = _
    rw [CFSG.KS.SporSch.J4B.vec_enc J4Real.hK J4InvP.pB.1.1, J4InvP.pB.1.2]
    rfl
  · have e : letter a b (codeL (k + 3)) = b⁻¹ := by simp [letter, codeL]
    rw [e, inv_smul_toRow (rep_invP hb), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    change toRow (toVecD 112 (CFSG.Sporadic.SmallF2.Native.vecMulN 112 Bn.2 s)) = _
    rw [CFSG.KS.SporSch.J4B.vec_enc J4Real.hK J4InvP.pB.2.1, J4InvP.pB.2.2]

theorem walk_ab : ∀ (w : List ℕ) (s : ℕ),
    (signedWord a b (toI w))⁻¹ • toRow (toVecD 112 s) =
      toRow (toVecD 112 (walkK rm A A B Bi w s))
  | [], s => by
    change (signedWord a b [])⁻¹ • _ = _
    simp [signedWord]
    rfl
  | k :: w, s => by
    have e : signedWord a b (toI (k :: w)) = letter a b (codeL k) * signedWord a b (toI w) := by
      simp [signedWord, toI]
    rw [e, mul_inv_rev, mul_smul, letter_inv_smul_ab, walk_ab w]
    change _ = toRow (toVecD 112 (CFSG.KC.Enum.strictN _ (walkK _ _ _ _ _ w)))
    rw [sN]

theorem ptR_77 : m77⁻¹ • v = ptR 77 := by
  rw [v, walk_ab, ptR, Nat.eq_of_beq_eq_true p77]

end W77

section Tree

theorem PR_cg {g : ℕ} (hg : g < 2) : PR (cg g) (nth 0 CGM g) := by
  have hw : ∀ n ∈ nth [] CGW g, n < 32 := by
    interval_cases g <;> decide +kernel
  have h := PR_gw hw
  rw [Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec cg_ok g hg)] at h
  exact h

theorem cg_mem {g : ℕ} (hg : g < 2) : cg g ∈ Subgroup.centralizer ({cE} : Set J) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact PR_eq_of_beq (PR_mul (PR_cg hg) PR_cE) (PR_mul PR_cE (PR_cg hg))
    (CFSG.KS.allN_spec comm_ok g hg)

theorem ce_reach {i : ℕ} (hi : i < 737) :
    ∃ g ∈ Subgroup.centralizer ({cE} : Set J), g • ptR (ptRoot i) = ptR i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h0 : i = 0
    · subst h0
      exact ⟨1, Subgroup.one_mem _, by simp [ptRoot]⟩
    by_cases h77 : i = 77
    · subst h77
      exact ⟨1, Subgroup.one_mem _, by simp [ptRoot]⟩
    obtain ⟨hp, hg, hb, hv⟩ := treeAt_spec (CFSG.KS.allN_spec tree_ok i hi) h0 h77
    have hroot : ptRoot (nth (0, 0) PAR i).1 = ptRoot i := by
      unfold ptRoot
      by_cases hi77 : i < 77
      · simp only [hb.2 hi77, hi77, ↓reduceIte]
      · have h1 : ¬ ((nth (0, 0) PAR i).1 < 77) := fun h => hi77 (hb.1 h)
        simp only [h1, hi77, ↓reduceIte]
    obtain ⟨g, hgC, hgv⟩ := ih _ hp (by omega)
    refine ⟨(cg (nth (0, 0) PAR i).2)⁻¹ * g,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (cg_mem hg)) hgC, ?_⟩
    rw [mul_smul, ← hroot, hgv, ptR, inv_smul_PR (PR_cg hg) (pt_lt (by omega)), hv]
    rfl

end Tree

section All

open scoped Classical

theorem ptR_mem {i : ℕ} (hi : i < 737) : ptR i ∈ orbit J v := by
  obtain ⟨g, -, hg⟩ := ce_reach hi
  by_cases h : i < 77
  · have e : ptRoot i = 0 := by simp [ptRoot, h]
    rw [e, ptR_zero] at hg
    exact ⟨g, hg⟩
  · have e : ptRoot i = 77 := by simp [ptRoot, h]
    rw [e, ← ptR_77, smul_smul] at hg
    exact ⟨g * m77⁻¹, hg⟩

theorem ptSet_fixed : ∀ p ∈ ptSet, p ∈ orbit J v ∧ cE • p = p := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
  exact ⟨ptR_mem (Finset.mem_range.1 hi), pt_fixed (Finset.mem_range.1 hi)⟩

end All

end Points

end CertificateChecks.KernelJ4Count.FixCE

end
