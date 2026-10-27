module

public import Certificates.Kernel.U43Seven.Checks
public import Certificates.Kernel.KsEight.CentGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Seven.G

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.HSStd.U43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut CertificateChecks.KernelU43Seven
open CertificateChecks.KernelCU43Aut.CentG CertificateChecks.KernelCU43Aut.SylG
open CertificateChecks.KernelKsEight.CentG8


theorem rep_of_bind' {p : Nat} {t : Array Nat} {g : Equiv.Perm (Fin 820)}
    (hb : bindListK 820 10 p t.toList = true) (hp : PR p g) : Rep 820 t g := by
  rw [arr_of_bind hb]
  exact Raw.Orb.rep_unpack hp

theorem ord7_facts {r : Nat} {ρ : Equiv.Perm (Fin 820)} (hc : cK r = true) (hr : PR r ρ)
    (h : ord7K r = true) : ρ ^ 7 = 1 ∧ ρ ≠ 1 := by
  unfold ord7K at h
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h7, h1⟩ := h
  refine ⟨?_, fun e => ?_⟩
  · have e7 : ρ ^ 7 = ρ * (ρ * (ρ * (ρ * (ρ * (ρ * ρ))))) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e7]
    exact pr_eq (pr_pc hr (pr_pc hr (pr_pc hr (pr_pc hr (pr_pc hr (pr_pc hr hr)))))) pr_pidn
      (Nat.eq_of_beq_eq_true h7)
  · rw [e] at hr
    have hq := canon_eq hc cK_pidn hr pr_pidn
    rw [hq, Nat.beq_refl] at h1
    exact absurd h1 (by decide)

theorem w7_data : ∃ γ : Equiv.Perm (Fin 820), Rep 820 w7Arr γ ∧ γ ∈ P ∧ γ ^ 7 = 1 ∧ γ ≠ 1 ∧
    Nat.card ↥(P ⊓ centralizer ({γ} : Set (Equiv.Perm (Fin 820)))) = 7 := by
  have h := w7Ok
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨γ, hγ, hγP⟩ := mem_P h1 h2
  have hc := w7Conj
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
  obtain ⟨g1, g2, g3⟩ := hc
  obtain ⟨g, hg, hgP⟩ := mem_P g1 g2
  have hw := pr_conj hg hγ (Nat.eq_of_beq_eq_true g3)
  have hcard := card_of_bounds hw kUW kLW
  rw [card_inf_centralizer_conj hgP] at hcard
  exact ⟨γ, rep_of_bind' w7Bind hγ, hγP, (ord7_facts h1 hγ h3).1, (ord7_facts h1 hγ h3).2, hcard⟩

theorem w7Check_true : w7Check = true := by
  obtain ⟨γ, hr, hγP, h7, h1, hcard⟩ := w7_data
  have e1 : isInvA 820 w7Arr (invCand 820 w7Arr) = true := isInvA_of_rep hr (rep_invCand hr)
  have e2 : inP w7Arr = true := (inP_iff hr).2 hγP
  have e3 : eqA 820 (powA 820 w7Arr 7) (idA 820) = true := (eqA_iff (rep_powA hr 7) rep_idA).2 h7
  have e4 : eqA 820 w7Arr (idA 820) = false := by
    cases e : eqA 820 w7Arr (idA 820)
    · rfl
    · exact absurd ((eqA_iff hr rep_idA).1 e) h1
  have e5 : countW (commW (idA 820) [w7Arr]) blocks [] = 7 := by
    rw [← card_eq_countW_P (f := commW (idA 820) [w7Arr]) (Pr := fun g => g * γ = γ * g)]
    · rw [← hcard]
      refine Nat.card_congr ?_
      exact
        { toFun := fun y => ⟨y.1.1, mem_inf.2 ⟨y.1.2, mem_centralizer_singleton_iff.2 y.2⟩⟩
          invFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, by
            exact mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2⟩
          left_inv := fun y => rfl
          right_inv := fun x => rfl }
    · intro w g hw _
      have hH : RepW 820 (idA 820 :: w) (g * 1) := RepW.cons rep_idA hw
      rw [mul_one] at hH
      simp only [commW, List.all_cons, List.all_nil, Bool.and_true]
      exact allLt_comm_iff hH hr
  unfold w7Check
  rw [e1, e2, e3, e4, e5]
  rfl

end CertificateChecks.KernelU43Seven.G

end
