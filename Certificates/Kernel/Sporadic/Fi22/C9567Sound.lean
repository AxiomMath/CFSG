module

public import Certificates.Kernel.Sporadic.Fi22.C9567
public import Certificates.Kernel.Sporadic.Fi22.C9554Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C9567

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W
open CertificateChecks.KernelSpor.Fi22C9554 CertificateChecks.KernelSpor.Fi22FiveK

theorem exists_word {A B AI BI : Nat} {G₁ G₂ : Equiv.Perm (Fin 3510)}
    (rA : Rep 3510 (unpack 3510 12 A) G₁) (rB : Rep 3510 (unpack 3510 12 B) G₂)
    (p2 : allN 2 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (two A B j) (two AI BI j)) = true)
    {w : List Int} (hl : lettersK 2 w = true) :
    ∃ E ∈ Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))),
      Rep 3510 (unpack 3510 12 (wd (two A B) (two AI BI) w)) E := by
  set Γ := Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))) with hΓ
  have pA : permOK 3510 12 (mask 12) (3510 * 12) A AI = true := allN_spec p2 0 (by norm_num)
  have pB : permOK 3510 12 (mask 12) (3510 * 12) B BI = true := allN_spec p2 1 (by norm_num)
  let S2 : Array (Array Nat) := #[unpack 3510 12 A, unpack 3510 12 B]
  have hS2 : S2.size = 2 ∧ ∀ j < 2, S2[j]! = unpack 3510 12 (two A B j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j
    · simp [S2, two]
    · simp [S2, two]
  let Gs : ℕ → Equiv.Perm (Fin 3510) := fun k => if k = 0 then G₁ else G₂
  have hGs : ∀ k < 2, Rep 3510 S2[k]! (Gs k) := by
    intro k hk
    interval_cases k
    · simpa [S2, Gs] using rA
    · simpa [S2, Gs] using rB
  have hGsI : ∀ k < 2, Rep 3510 (rawInvs 3510 S2)[k]! (Gs k)⁻¹ := by
    intro k hk
    interval_cases k
    · have e : (rawInvs 3510 S2)[0]! = unpack 3510 12 AI := by
        simp only [rawInvs, S2]
        simpa using (invEqK_sound pA).1
      rw [e]
      exact rep_inv rA pA
    · have e : (rawInvs 3510 S2)[1]! = unpack 3510 12 BI := by
        simp only [rawInvs, S2]
        simpa using (invEqK_sound pB).1
      rw [e]
      exact rep_inv rB pB
  have hGsK : ∀ k < 2, Gs k ∈ Γ := by
    intro k hk
    interval_cases k
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hl' : lettersOK 2 w = true := (wordEqK_sound hS2 p2 (r := wd (two A B) (two AI BI) w)
    (by rw [wordEqK]; simp only [bAnd_iff, szOK', hl, true_and]; exact Nat.beq_refl _)).2
  obtain ⟨E, hE, rE⟩ := exists_rep_wordA hGs hGsI hGsK w hl'
  rw [wd_eq hS2 p2 hl] at rE
  exact ⟨E, hE, rE⟩

theorem rep_pwK {P : Nat} {g : Equiv.Perm (Fin 3510)} (hc : Fi22X.cn P = true)
    (h : Rep 3510 (unpack 3510 12 P) g) (k : Nat) :
    Rep 3510 (unpack 3510 12 (pwK P k)) (g ^ k) ∧ Fi22X.cn (pwK P k) = true := by
  obtain ⟨e, c⟩ := pw_eq hc k
  rw [← e]
  exact ⟨rep_pw h k, c⟩

theorem eq_one_of {P : Nat} {g : Equiv.Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 P) g)
    (he : Nat.beq P (pidn 3510 12) = true) : g = 1 := by
  rw [Nat.eq_of_beq_eq_true he, ← hI] at h
  exact h.unique rep_idA

theorem ne_one_of {P : Nat} {g : Equiv.Perm (Fin 3510)} (hc : Fi22X.cn P = true)
    (h : Rep 3510 (unpack 3510 12 P) g) (he : Nat.beq P (pidn 3510 12) = false) : g ≠ 1 := by
  intro h1
  rw [h1] at h
  have e := (eqA_iff h (hI ▸ rep_idA)).2 rfl
  rw [eqA_unpack hc cnId, he] at e
  exact Bool.false_ne_true e

theorem e9 {G₁ G₂ : Equiv.Perm (Fin 3510)} (h₁ : Rep 3510 g1A G₁) (h₂ : Rep 3510 g2A G₂) :
    ∃ a ∈ Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))),
      ∃ b ∈ Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))),
        a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
          ∀ i j : ℕ, i < 3 → j < 3 → (i ≠ 0 ∨ j ≠ 0) → a ^ i * b ^ j ≠ 1 := by
  have hk := ok
  unfold all9567 at hk
  simp only [Fi22C9554.strictB_eq] at hk
  unfold core at hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨p6, p2⟩, cA⟩, cB⟩, a3⟩, b3⟩, hc⟩, -⟩, -⟩, -⟩, -⟩, hnt⟩ := hk
  obtain ⟨hgA, hgB⟩ := g_eq p6 x_eq y_eq h_eq n1_eq n2_eq z_eq
  rw [hgA] at h₁
  rw [hgB] at h₂
  have rA := h₁
  have rB := h₂
  have hl : lettersK 2 e9W1 = true ∧ lettersK 2 e9W2 = true := (bAnd_iff _ _).1 lettersE
  obtain ⟨a, ha, ra⟩ := exists_word rA rB p2 hl.1
  obtain ⟨b, hb, rb⟩ := exists_word rA rB p2 hl.2
  refine ⟨a, ha, b, hb, eq_one_of (rep_pwK cA ra 3).1 a3, eq_one_of (rep_pwK cB rb 3).1 b3, ?_, ?_⟩
  · have e := congrArg (unpack 3510 12) (Nat.eq_of_beq_eq_true hc)
    rw [← Fi22X.comp_eq cA cB, ← Fi22X.comp_eq cB cA] at e
    have r1 := rep_compA ra rb
    rw [e] at r1
    exact r1.unique (rep_compA rb ra)
  · intro i j hi hj hij
    have hs := allN_spec (allN_spec hnt i hi) j hj
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
    rcases hs with ⟨h0, h0'⟩ | hs
    · rcases hij with h | h
      · exact absurd h0 h
      · exact absurd h0' h
    · obtain ⟨ri, ci⟩ := rep_pwK cA ra i
      obtain ⟨rj, cj⟩ := rep_pwK cB rb j
      have r := rep_compA ri rj
      rw [Fi22X.comp_eq ci cj] at r
      exact ne_one_of (Fi22X.cn_c ci cj) r hs

end CertificateChecks.KernelSpor.Fi22C9567

end
