module

public import Certificates.Kernel.SporCovLane.HN
public import Certificates.Kernel.HNF26720.Facts
public import CFSG.Certificates.Kernel.SporCov.LaneKit
public import CFSG.Certificates.Kernel.SporCov.PcCl
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses
public import CFSG.Sporadic.HNSchreier.Intrinsic
import Certificates.Kernel.HN3166.Seed
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
import Mathlib

public section

namespace CFSG.KD.SporCovLane.HN

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.KC.Ord CFSG.KS.Ord CFSG.StandardType.SporadicShape
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CertificateChecks.KernelHNF26720
open CFSG.Sporadic.F5

theorem complete_of_two {K : Type} [Group K] {p : ℕ} {s₀ s₁ t₀ t₁ : K}
    (hcl : ∀ x : K, orderOf x = p → IsConj s₀ x ∨ IsConj s₁ x) (h₀ : orderOf t₀ = p)
    (h₁ : orderOf t₁ = p) (hne : ¬ IsConj t₀ t₁) :
    ∀ x : K, orderOf x = p → IsConj t₀ x ∨ IsConj t₁ x := by
  intro x hx
  rcases hcl t₀ h₀ with a | a <;> rcases hcl t₁ h₁ with b | b
  · exact absurd (a.symm.trans b) hne
  · rcases hcl x hx with c | c
    · exact Or.inl (a.symm.trans c)
    · exact Or.inr (b.symm.trans c)
  · rcases hcl x hx with c | c
    · exact Or.inr (b.symm.trans c)
    · exact Or.inl (a.symm.trans c)
  · exact absurd (a.symm.trans b) hne

theorem nthW_RA0 : nthW D.RA 0 = [0] := by decide

theorem nthW_RA1 : nthW D.RA 1 = [2] := by decide

theorem nthW_RB0 : nthW D.RB 0 = [0] := by decide

theorem nthW_RB1 : nthW D.RB 1 = [2] := by decide

theorem sporKRestCover_three_JH :
    SporKRestCover 3 ↥JH := by
  have : Finite ↥JH := Finite.of_injective ρJ ρJ_injective
  have vB := CertificateChecks.KernelHN.s_v2
  have vBi := (CFSG.KS.J4Hub.mul_sound' (hnb := rfl) CFSG.KD.FamHNSeed.consts vB vB).1
  have hA : ordMat 5 133 13 1729 (CFSG.KD.FamHNSeed.RW 1) = ρJ aJ :=
    ((ρJ_apply aJ).trans matJ_aJ).symm
  have hB : ordMat 5 133 13 1729 (CFSG.KD.FamHNSeed.RW 2) = ρJ bJ :=
    ((ρJ_apply bJ).trans matJ_bJ).symm
  obtain ⟨mw, hk, hmw⟩ := kitLn_sound CFSG.KD.FamHNSeed.consts (nb := 229957) rfl
    CertificateChecks.KernelHN.s_v1 CertificateChecks.KernelHN.s_v1 vB vBi hA hB Ck.ok
  obtain ⟨hM, hcomp⟩ := eqM_model CFSG.KD.FamHNSeed.consts (nb := 229957) rfl ρJ_injective hmw
  set ev := wE (fLn aJ bJ D.Ws) with hev
  have hab : ev [0] = aJ ∧ ev [2] = bJ := by
    refine ⟨?_, ?_⟩ <;> simp [hev, wE, fLn, f4]
  have hgen : Subgroup.closure ({aJ, bJ} : Set ↥JH) = ⊤ := closure_ab hnsData
  have htop : ∀ (R : List (List ℕ)), nthW R 0 = [0] → nthW R 1 = [2] →
      ∀ T : Subgroup ↥JH, (∀ k, ev (nthW R k) ∈ T) → T = ⊤ := by
    intro R h0 h1 T hT
    have ha := hT 0
    have hb := hT 1
    rw [h0, hab.1] at ha
    rw [h1, hab.2] at hb
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hb
  unfold chk at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨kA, kB⟩, ktr⟩ := hk
  obtain ⟨oA, gA⟩ := hM.generating_of_pccOK Nat.prime_three (by norm_num) hcomp kA
    (htop _ nthW_RA0 nthW_RA1)
  obtain ⟨oB, gB⟩ := hM.generating_of_pccOK Nat.prime_three (by norm_num) hcomp kB
    (htop _ nthW_RB0 nthW_RB1)
  have hne : ¬ IsConj (ev D.TA) (ev D.TB) := by
    intro hcj
    have e := trace_conj ρJ hcj
    rw [← (hmw D.TA).2, ← (hmw D.TB).2, ← trR_eq, ← trR_eq] at e
    have e' : Nat.mod (trR 13 1729 133 (mw D.TA)) 5 = Nat.mod (trR 13 1729 133 (mw D.TB)) 5 :=
      (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
    rw [e', Nat.beq_refl] at ktr
    exact absurd ktr (by decide)
  have hall := complete_of_two (fun x hx => (order_three_classes x).1 hx) oA oB hne
  refine sporKRest_cover_of_classes Nat.prime_three [ev D.TA, ev D.TB] (fun s hs => ?_) ?_
  · rcases hall s hs with h | h
    · exact ⟨_, List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
  · intro r hr x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact gA x hx
    · exact gB x hx

end CFSG.KD.SporCovLane.HN

end
