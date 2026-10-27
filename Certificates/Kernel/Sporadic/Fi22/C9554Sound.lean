module

public import Certificates.Kernel.Sporadic.Fi22.C9554
public import Certificates.Kernel.Sporadic.Fi22.FiveK
public import CFSG.Certificates.Kernel.OrbChainSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C9554

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.OrbChain
open CFSG.KC.Census CFSG.KC.Census.Base
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem wd_eq {kS : Nat} {S : Array (Array Nat)} {PS PSI : Nat → Nat}
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack 3510 12 (PS j))
    (hp : allN kS (fun j => permOK 3510 12 (mask 12) (3510 * 12) (PS j) (PSI j)) = true)
    {w : List Int} (hl : lettersK kS w = true) :
    wordA 3510 S (rawInvs 3510 S) w = unpack 3510 12 (wd PS PSI w) := by
  refine (wordEqK_sound hS hp ?_).1
  rw [wordEqK]
  simp only [bAnd_iff, szOK', hl, true_and]
  exact Nat.beq_refl _

theorem at_of_rep {P : Nat} {g : Equiv.Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 P) g)
    (p : Nat) (hp : p < 3510) : at' 12 P p = (g ⟨p, hp⟩ : ℕ) := by
  unfold at'
  rw [← CFSG.KS.Raw.Orb.unpack_get hp]
  exact h.apply hp

theorem rep_inv {P PI : Nat} {g : Equiv.Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 P) g)
    (hp : permOK 3510 12 (mask 12) (3510 * 12) P PI = true) :
    Rep 3510 (unpack 3510 12 PI) g⁻¹ :=
  rep_inv_of_isInvA h (invEqK_sound hp).2

theorem letters_g : lettersK 6 g1w = true ∧ lettersK 6 g2w = true := (bAnd_iff _ _).1 lettersG

theorem letters_h : lettersK 2 h1w = true ∧ lettersK 2 h2w = true := (bAnd_iff _ _).1 lettersH

theorem g_eq {X Y H N1 N2 Z : Nat}
    (hp : allN 6 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (six X Y H N1 N2 Z j)
      (Fi22X.inv (six X Y H N1 N2 Z j))) = true)
    (hX : xA = unpack 3510 12 X) (hY : yA = unpack 3510 12 Y) (hH : hA = unpack 3510 12 H)
    (h1 : n1A = unpack 3510 12 N1) (h2 : n2A = unpack 3510 12 N2)
    (hZ : zA = unpack 3510 12 Z) :
    g1A = unpack 3510 12 (wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g1w) ∧
    g2A = unpack 3510 12 (wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g2w) := by
  have hS : gens6A.size = 6 ∧ ∀ j < 6, gens6A[j]! = unpack 3510 12 (six X Y H N1 N2 Z j) := by
    refine ⟨by simp [gens6A], fun j hj => ?_⟩
    interval_cases j
    · have e : gens6A[0]! = xA := by simp [gens6A]
      rw [e]
      exact hX
    · have e : gens6A[1]! = yA := by simp [gens6A]
      rw [e]
      exact hY
    · have e : gens6A[2]! = hA := by simp [gens6A]
      rw [e]
      exact hH
    · have e : gens6A[3]! = n1A := by simp [gens6A]
      rw [e]
      exact h1
    · have e : gens6A[4]! = n2A := by simp [gens6A]
      rw [e]
      exact h2
    · have e : gens6A[5]! = zA := by simp [gens6A]
      rw [e]
      exact hZ
  exact ⟨wd_eq hS hp letters_g.1, wd_eq hS hp letters_g.2⟩

theorem bound_of_core {X Y H N1 N2 Z A B C D AI BI CI DI : Nat}
    {G₁ G₂ : Equiv.Perm (Fin 3510)} (hX : xA = unpack 3510 12 X) (hY : yA = unpack 3510 12 Y)
    (hH : hA = unpack 3510 12 H) (h1 : n1A = unpack 3510 12 N1)
    (h2 : n2A = unpack 3510 12 N2) (hZ : zA = unpack 3510 12 Z)
    (hAe : A = wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g1w)
    (hBe : B = wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g2w)
    (hCe : C = wd (two A B) (two AI BI) h1w) (hDe : D = wd (two A B) (two AI BI) h2w)
    (h₁ : Rep 3510 g1A G₁) (h₂ : Rep 3510 g2A G₂)
    (hc : core X Y H N1 N2 Z A B C D AI BI CI DI = true) :
    1045094400 ≤ Nat.card (Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510)))) := by
  unfold core at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨p6, p2⟩, pC⟩, pD⟩, hch⟩ := hc
  set Γ := Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))) with hΓ
  obtain ⟨hgA, hgB⟩ := g_eq p6 hX hY hH h1 h2 hZ
  rw [← hAe] at hgA
  rw [← hBe] at hgB
  have rA : Rep 3510 (unpack 3510 12 A) G₁ := by
    rw [← hgA]
    exact h₁
  have rB : Rep 3510 (unpack 3510 12 B) G₂ := by
    rw [← hgB]
    exact h₂
  have pA : permOK 3510 12 (mask 12) (3510 * 12) A AI = true := allN_spec p2 0 (by norm_num)
  have pB : permOK 3510 12 (mask 12) (3510 * 12) B BI = true := allN_spec p2 1 (by norm_num)
  have rAI := rep_inv rA pA
  have rBI := rep_inv rB pB
  let S2 : Array (Array Nat) := #[unpack 3510 12 A, unpack 3510 12 B]
  have hS2 : S2.size = 2 ∧ ∀ j < 2, S2[j]! = unpack 3510 12 (two A B j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j
    · simp [S2, two]
    · simp [S2, two]
  let Gs : ℕ → Equiv.Perm (Fin 3510) := fun k => if k = 0 then G₁ else G₂
  have hG1 : G₁ ∈ Γ := Subgroup.subset_closure (Set.mem_insert _ _)
  have hG2 : G₂ ∈ Γ := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
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
      exact rAI
    · have e : (rawInvs 3510 S2)[1]! = unpack 3510 12 BI := by
        simp only [rawInvs, S2]
        simpa using (invEqK_sound pB).1
      rw [e]
      exact rBI
  have hGsK : ∀ k < 2, Gs k ∈ Γ := by
    intro k hk
    interval_cases k
    · exact hG1
    · exact hG2
  obtain ⟨H₁, hH₁, rH₁⟩ := exists_rep_wordA hGs hGsI hGsK h1w (by decide +kernel)
  obtain ⟨H₂, hH₂, rH₂⟩ := exists_rep_wordA hGs hGsI hGsK h2w (by decide +kernel)
  rw [wd_eq hS2 p2 letters_h.1, ← hCe] at rH₁
  rw [wd_eq hS2 p2 letters_h.2, ← hDe] at rH₂
  have rCI := rep_inv rH₁ pC
  have rDI := rep_inv rH₂ pD
  let ℓ : ℕ → Equiv.Perm (Fin 3510) := fun k =>
    [G₁, G₂, H₁, H₂, G₁⁻¹, G₂⁻¹, H₁⁻¹, H₂⁻¹].getD k 1
  have HL : Letters 3510 12 4 (lt8 A B C D AI BI CI DI) ℓ := by
    refine ⟨fun k hk p hp => ?_, fun k hk => ?_⟩
    · interval_cases k
      · exact at_of_rep rA p hp
      · exact at_of_rep rB p hp
      · exact at_of_rep rH₁ p hp
      · exact at_of_rep rH₂ p hp
      · exact at_of_rep rAI p hp
      · exact at_of_rep rBI p hp
      · exact at_of_rep rCI p hp
      · exact at_of_rep rDI p hp
    · interval_cases k <;> rfl
  have hℓ : ∀ k < 2 * 4, ℓ k ∈ Γ := by
    intro k hk
    interval_cases k
    · exact hG1
    · exact hG2
    · exact hH₁
    · exact hH₂
    · exact Γ.inv_mem hG1
    · exact Γ.inv_mem hG2
    · exact Γ.inv_mem hH₁
    · exact Γ.inv_mem hH₂
  exact le_card_of_chainOK HL hℓ hch

theorem card_ge {G₁ G₂ : Equiv.Perm (Fin 3510)} (h₁ : Rep 3510 g1A G₁) (h₂ : Rep 3510 g2A G₂) :
    1045094400 ≤ Nat.card (Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510)))) := by
  have hk := ok
  unfold all9554 at hk
  simp only [strictB_eq] at hk
  exact bound_of_core Fi22FiveK.x_eq Fi22FiveK.y_eq Fi22FiveK.h_eq Fi22FiveK.n1_eq
    Fi22FiveK.n2_eq Fi22FiveK.z_eq rfl rfl rfl rfl h₁ h₂ hk

end CertificateChecks.KernelSpor.Fi22C9554

end
