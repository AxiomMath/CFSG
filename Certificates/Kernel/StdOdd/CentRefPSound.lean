module

public import Certificates.Kernel.StdOdd.CentRefP
public import CFSG.Certificates.Kernel.StdOdd.ChainPSound

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.StdOdd.ChainP CFSG.KS.StdOdd.Orbit
  CFSG.KS.StdOdd.Chain CFSG.KS.StdOdd.ChainP

theorem rchP_sound (D : CentData) {A B RK K ri : ℕ} {O : List ℕ} {Sr : List (List (List ℕ))}
    {l k : ℕ} (h : D.rchP A B RK K ri O Sr l k = true) : D.rchF A B RK K ri O Sr l k = true := by
  unfold CentData.rchP at h
  rw [forceLB_eq] at h
  beta_reduce at h
  rw [andB_eq, Bool.and_eq_true, forceB_eq] at h
  beta_reduce at h
  obtain ⟨hb, hw⟩ := h
  rw [walkP_eq _ _ _ (bd_of_bdB _ hb) (lenN_rkP D RK K ri O _)] at hw
  unfold CentData.rchF
  exact hw

theorem flatC_mono {L K : ℕ} {fl : ℕ → ℕ} {F G : ℕ → ℕ → ℕ → Bool}
    (hFG : ∀ a b c, F a b c = true → G a b c = true) {q : ℕ} (h : flatC L K fl F q = true) :
    flatC L K fl G q = true := by
  unfold flatC at h ⊢
  revert h
  cases Nat.blt (q / K % L) (fl (q / (L * K)))
  · intro _
    rfl
  · exact hFG (q / (L * K)) (q / K % L) (q % K)

end CFSG.KD.StdOdd.Cent

end
