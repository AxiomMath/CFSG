module

public import Certificates.Kernel.LocalComp.WittA8165
public import Certificates.Kernel.LocalComp.WittK8164

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign
  CertificateChecks.KernelSpor.M22Syl CFSG.RankThree.PartTwo.KFacts.KP4

theorem count_trQ (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q]
    (w : List Bool) (e₀ e₁ e₂ : Fin 22) (h₀ : pt (pwp A B I w) e₀.val = 0)
    (h₁ : pt (pwp A B I w) e₁.val = 1) (h₂ : pt (pwp A B I w) e₂.val = 2) (C0 : Nat → Bool)
    (C1 : Nat → Nat → Bool) (C2 : Nat → Nat → Nat → Bool)
    (hQ : ∀ f : Perm (Fin 22), Q ⇑f →
      C0 (f e₀).val = true ∧ C1 (f e₀).val (f e₁).val = true ∧
        C2 (f e₀).val (f e₁).val (f e₂).val = true) :
    m22Count Q = wc Q (pwp A B I w) C0 C1 C2 := by
  refine m22Count_eq_wc Q (wordPerm w) (wordPerm_mem w) _ (pkw_wordPerm w) C0 C1 C2
    fun σ h => ?_
  have := hQ _ h
  rwa [mul_apply_of_pk (pkw_wordPerm w) σ (i := 0) h₀,
    mul_apply_of_pk (pkw_wordPerm w) σ (i := 1) h₁,
    mul_apply_of_pk (pkw_wordPerm w) σ (i := 2) h₂] at this

theorem facts8164 :
    m22Count (fun f => (∀ p, f (ofTab deltaTab (ofTab (lineTab 0) p)) =
        ofTab (lineTab 0) (f (ofTab deltaTab p))) ∧
      ∀ p, f (ofTab deltaTab (ofTab (lineTab 1) p)) =
        ofTab (lineTab 1) (f (ofTab deltaTab p))) = 0 := by
  refine (count_trQ _ wD 13 19 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    _ fun f hf => ?_).trans k8164
  have l00 : ofTab (lineTab 0) 0 = 0 := by decide +kernel
  have l10 : ofTab (lineTab 1) 0 = 0 := by decide +kernel
  have l014 : ofTab (lineTab 0) 14 = 14 := by decide +kernel
  have l18 : ofTab (lineTab 1) 8 = 8 := by decide +kernel
  have d0 : ofTab deltaTab 0 = 13 := by decide +kernel
  have d14 : ofTab deltaTab 14 = 19 := by decide +kernel
  have d8 : ofTab deltaTab 8 = 11 := by decide +kernel
  have m0 : ∀ x : Fin 22, x = ofTab (lineTab 0) x → x = ofTab (lineTab 1) x →
      Nat.beq x.val 0 = true := by decide +kernel
  have m1 : ∀ x : Fin 22, x = ofTab (lineTab 0) x → inM 1097729 x.val = true := by
    decide +kernel
  have m2 : ∀ x : Fin 22, x = ofTab (lineTab 1) x → inM 2098433 x.val = true := by
    decide +kernel
  have a0 := hf.1 0
  have b0 := hf.2 0
  have a14 := hf.1 14
  have b8 := hf.2 8
  rw [l00, d0] at a0
  rw [l10, d0] at b0
  rw [l014, d14] at a14
  rw [l18, d8] at b8
  exact ⟨m0 _ a0 b0, m1 _ a14, m2 _ b8⟩

end CertificateChecks.KernelLC.Witt

end
