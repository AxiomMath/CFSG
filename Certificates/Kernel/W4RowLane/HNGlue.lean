module

public import CFSG.Sporadic.HNOddCore.RAction
public import Certificates.Kernel.HNF26720.Facts
import Certificates.Kernel.W4RowLane.HN
import CFSG.Certificates.Kernel.SporCov.OrdP
import CFSG.Certificates.Kernel.SporCov.LaneKit
import CFSG.Certificates.Kernel.SporCov.Words
import CFSG.Certificates.Kernel.Spor.OrdCanon
import Certificates.Kernel.HN3166.Seed
import Certificates.Kernel.SporSch.HN.PtCR
import Certificates.Kernel.VecCert.WordProg
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
import Mathlib

public section

namespace CFSG.KD.W4RowLane.HN

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CertificateChecks.KernelHNF26720

private theorem f4_invL {G : Type} [Group G] (x y : G) {c : ℕ} (hc : c < 4) :
    f4 x y (invL c) = (f4 x y c)⁻¹ := by
  interval_cases c <;> simp [f4, invL]

private theorem wE_invK {G : Type} [Group G] (x y : G) :
    ∀ u : List ℕ, (∀ c ∈ u, c < 4) → wE (fLn x y []) (invK u) = (wE (fLn x y []) u)⁻¹
  | [], _ => by simp [invK, wE]
  | c :: u, hu => by
    have hc : c < 4 := hu c List.mem_cons_self
    have e : invK (c :: u) = invK u ++ [invL c] := by simp [invK]
    have hl : invL c < 4 := by unfold invL; split <;> omega
    rw [e, wE_append, wE_cons, wE_nil, one_mul, wE_cons,
      wE_invK x y u fun d hd => hu d (List.mem_cons_of_mem _ hd), mul_inv_rev]
    simp only [fLn, if_pos hl, if_pos hc]
    rw [f4_invL x y hc]

private theorem p19 : Nat.Prime 19 := by norm_num

private theorem lt_aK₁ : ∀ c ∈ aK₁, c < 4 := by decide

private theorem lt_aK₂ : ∀ c ∈ aK₂, c < 4 := by decide

private theorem lt_uK₁ : ∀ c ∈ uK₁, c < 4 := by decide

private theorem lt_uK₂ : ∀ c ∈ uK₂, c < 4 := by decide

private theorem lt_cK : ∀ c ∈ cK, c < 4 := by decide

variable {Gp : Type} [Group Gp] {ρ : Gp →* Matrix (Fin 133) (Fin 133) (ZMod 5)}

private theorem mul_ok {X Y : ℕ} {x y : Gp}
    (hX : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H X = true ∧
      ordMat 5 133 13 1729 X = ρ x)
    (hY : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H Y = true ∧
      ordMat 5 133 13 1729 Y = ρ y) :
    validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (mul X Y) = true ∧
      ordMat 5 133 13 1729 (mul X Y) = ρ (x * y) := by
  obtain ⟨v, e⟩ := mul_sound' CFSG.KD.FamHNSeed.consts rfl hX.1 hY.1
  exact ⟨v, by rw [e, hX.2, hY.2, map_mul]⟩

private theorem kit_facts : ∃ mw : List ℕ → ℕ, chk (CFSG.KD.HNPtC.GT 10) mw = true ∧
    ∀ u, validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (mw u) = true ∧
      ordMat 5 133 13 1729 (mw u) = ρJ (wE (fLn aJ bJ []) u) := by
  have vB := CertificateChecks.KernelHN.s_v2
  have vBi := (mul_sound' (hnb := rfl) CFSG.KD.FamHNSeed.consts vB vB).1
  have hA : ordMat 5 133 13 1729 (CFSG.KD.FamHNSeed.RW 1) = ρJ aJ :=
    ((ρJ_apply aJ).trans matJ_aJ).symm
  have hB : ordMat 5 133 13 1729 (CFSG.KD.FamHNSeed.RW 2) = ρJ bJ :=
    ((ρJ_apply bJ).trans matJ_bJ).symm
  exact kitLn_sound CFSG.KD.FamHNSeed.consts (nb := 229957) rfl CertificateChecks.KernelHN.s_v1
    CertificateChecks.KernelHN.s_v1 vB vBi hA hB Ck.ok

private theorem cjM_ok {mw : List ℕ → ℕ} {X : ℕ} {W : List ℕ} {x g : Gp}
    (hX : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H X = true ∧
      ordMat 5 133 13 1729 X = ρ x)
    (hg : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (mw W) = true ∧
      ordMat 5 133 13 1729 (mw W) = ρ g)
    (hgi : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (mw (invK W)) = true ∧
      ordMat 5 133 13 1729 (mw (invK W)) = ρ g⁻¹) :
    validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (cjM mw X W) = true ∧
      ordMat 5 133 13 1729 (cjM mw X W) = ρ (g * x * g⁻¹) :=
  mul_ok (mul_ok hg hX) hgi

private theorem in_sq {U : ℕ} {u : ↥JH}
    (hUu : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H U = true ∧
      ordMat 5 133 13 1729 U = ρJ u)
    (hU2 : Nat.beq (mul U U) CFSG.KD.FamHNSeed.ONE = true) : u ^ 2 = 1 := by
  have hc := CFSG.KD.FamHNSeed.consts
  obtain ⟨-, eO⟩ := one_sound' (nb := 229957) hc rfl
  apply ρJ_injective
  have hUU := Nat.eq_of_beq_eq_true hU2
  have eUU : ordMat 5 133 13 1729 (mul U U) = ordMat 5 133 13 1729 U * ordMat 5 133 13 1729 U :=
    (mul_sound' hc rfl hUu.1 hUu.1).2
  rw [hUU, eO] at eUU
  rw [map_pow, map_one, sq, ← hUu.2, ← eUU]

private theorem in_ne {U : ℕ} {u : ↥JH}
    (hUu : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H U = true ∧
      ordMat 5 133 13 1729 U = ρJ u)
    (hU1 : Nat.beq U CFSG.KD.FamHNSeed.ONE = false) : u ≠ 1 := by
  have hc := CFSG.KD.FamHNSeed.consts
  obtain ⟨vO, eO⟩ := one_sound' (nb := 229957) hc rfl
  intro h1
  have e : U = CFSG.KD.FamHNSeed.ONE :=
    ordMat_inj' hc rfl hUu.1 vO (by rw [hUu.2, h1, map_one, eO])
  rw [e, Nat.beq_refl] at hU1
  exact absurd hU1 (by decide)

private theorem in_nc {A U : ℕ} {u : ↥JH}
    (hA0 : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H A = true ∧
      ordMat 5 133 13 1729 A = ρJ aJ)
    (hUu : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H U = true ∧
      ordMat 5 133 13 1729 U = ρJ u)
    (htr : Nat.beq (tr5 A) (tr5 U) = false) : ¬IsConj aJ u := by
  intro hcj
  have e := trace_conj ρJ hcj
  rw [← hA0.2, ← hUu.2, ← trR_eq, ← trR_eq] at e
  have e' : tr5 A = tr5 U := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
  rw [e', Nat.beq_refl] at htr
  exact absurd htr (by decide)

private theorem in_tri {mw : List ℕ → ℕ}
    (hmw : ∀ u, validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (mw u) = true ∧
      ordMat 5 133 13 1729 (mw u) = ρJ (wE (fLn aJ bJ []) u))
    {X : ℕ} {x : ↥JH}
    (hX : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H X = true ∧
      ordMat 5 133 13 1729 X = ρJ x) {W₁ W₂ : List ℕ} (h₁ : ∀ c ∈ W₁, c < 4)
    (h₂ : ∀ c ∈ W₂, c < 4) (o : ordPK mul CFSG.KD.FamHNSeed.ONE (triM mw X W₁ W₂) 19 = true) :
    orderOf (x * (wE (fLn aJ bJ []) W₁ * x * (wE (fLn aJ bJ []) W₁)⁻¹) *
      (wE (fLn aJ bJ []) W₂ * x * (wE (fLn aJ bJ []) W₂)⁻¹)) = 19 := by
  have hI : ∀ W : List ℕ, (∀ c ∈ W, c < 4) →
      validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (mw (invK W)) = true ∧
        ordMat 5 133 13 1729 (mw (invK W)) = ρJ (wE (fLn aJ bJ []) W)⁻¹ := fun W hW =>
    ⟨(hmw _).1, by rw [(hmw _).2, wE_invK aJ bJ W hW]⟩
  have c1 := cjM_ok hX (hmw W₁) (hI W₁ h₁)
  have c2 := cjM_ok hX (hmw W₂) (hI W₂ h₂)
  have h := mul_ok (mul_ok hX c1) c2
  unfold triM at o
  exact ordPK_orderOf CFSG.KD.FamHNSeed.consts rfl ρJ_injective p19 (by norm_num) h.1 h.2 o

theorem hn_inner : ∃ u g₁ g₂ h₁ h₂ : ↥JH, u ^ 2 = 1 ∧ u ≠ 1 ∧ ¬IsConj aJ u ∧
    orderOf (aJ * (g₁ * aJ * g₁⁻¹) * (g₂ * aJ * g₂⁻¹)) = 19 ∧
    orderOf (u * (h₁ * u * h₁⁻¹) * (h₂ * u * h₂⁻¹)) = 19 := by
  have hc := CFSG.KD.FamHNSeed.consts
  have hs : CertificateChecks.KernelHomG.LayoutSound
      (fun X => validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H X = true)
      (ordMat 5 133 13 1729) mul (validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H)
      CFSG.KD.FamHNSeed.ONE :=
    ⟨fun _ _ hA hB => mul_sound' hc rfl hA hB, (one_sound' hc rfl).1, (one_sound' hc rfl).2,
      fun _ h => h⟩
  obtain ⟨mw, hk, hmw⟩ := kit_facts
  unfold chk at hk
  rw [forceR_eq] at hk
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
  obtain ⟨⟨⟨⟨⟨hU2, hU1⟩, htr⟩, o1⟩, o2⟩, -⟩ := hk
  have ha : wE (fLn aJ bJ []) [0] = aJ := by simp [wE, fLn, f4]
  have hA0 := hmw [0]
  rw [ha] at hA0
  obtain ⟨v, e⟩ := CertificateChecks.KernelWP.powR_sound hs (hmw uK).1 10
  generalize hU : powR mul CFSG.KD.FamHNSeed.ONE (mw uK) 10 = U at hU2 hU1 htr o2 v e
  obtain ⟨u, hu⟩ : ∃ u : ↥JH, u = wE (fLn aJ bJ []) uK ^ 10 := ⟨_, rfl⟩
  have e10 : (10 : ℕ) % 65536 = 10 := by norm_num
  have hUu : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H U = true ∧
      ordMat 5 133 13 1729 U = ρJ u := by
    refine ⟨v, ?_⟩
    rw [e, e10, (hmw uK).2, hu, map_pow]
  refine ⟨u, wE (fLn aJ bJ []) aK₁, wE (fLn aJ bJ []) aK₂, wE (fLn aJ bJ []) uK₁,
    wE (fLn aJ bJ []) uK₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact in_sq hUu hU2
  · exact in_ne hUu hU1
  · exact in_nc hA0 hUu htr
  · exact in_tri hmw hA0 lt_aK₁ lt_aK₂ o1
  · exact in_tri hmw hUu lt_uK₁ lt_uK₂ o2

theorem hn_outer :
    ∃ w : ↥JH, orderOf (cU * ((w : GL (Fin hnsData.d) (ZMod 5)) * cU *
      (w : GL (Fin hnsData.d) (ZMod 5))⁻¹)) = 19 := by
  have hc := CFSG.KD.FamHNSeed.consts
  obtain ⟨mw, hk, hmw⟩ := kit_facts
  unfold chk at hk
  rw [forceR_eq] at hk
  simp only [Bool.and_eq_true] at hk
  have o3 := hk.2
  let ρG : GL (Fin hnsData.d) (ZMod 5) →* Matrix (Fin 133) (Fin 133) (ZMod 5) :=
    Units.coeHom _
  have hρG : Function.Injective ρG := fun _ _ h => Units.ext h
  set ev := wE (fLn aJ bJ []) with hev
  have hg : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (mw cK) = true ∧
      ordMat 5 133 13 1729 (mw cK) = ρG ((ev cK : ↥JH) : GL (Fin hnsData.d) (ZMod 5)) :=
    ⟨(hmw cK).1, (hmw cK).2.trans rfl⟩
  have hgi : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (mw (invK cK)) = true ∧
      ordMat 5 133 13 1729 (mw (invK cK)) =
        ρG ((ev cK : ↥JH) : GL (Fin hnsData.d) (ZMod 5))⁻¹ := by
    have hinvE : ev (invK cK) = (ev cK)⁻¹ := wE_invK aJ bJ cK lt_cK
    refine ⟨(hmw _).1, ?_⟩
    rw [(hmw _).2, hinvE, ← Subgroup.coe_inv]
    rfl
  have hC : validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (CFSG.KD.HNPtC.GT 10) = true ∧
      ordMat 5 133 13 1729 (CFSG.KD.HNPtC.GT 10) = ρG cU :=
    ⟨CFSG.KS.OrdCanon.validM_of_canon hc
        (CertificateChecks.KernelSporSch.HNPtC.GT_canon (by norm_num)),
      by rw [CertificateChecks.KernelSporSch.HNPtC.C_mat, CFSG.Sporadic.HNOddCore.matR_cR]; rfl⟩
  have h := mul_ok hC (cjM_ok hC hg hgi)
  exact ⟨ev cK, ordPK_orderOf hc rfl hρG p19 (by norm_num) h.1 h.2 o3⟩

end CFSG.KD.W4RowLane.HN

end
