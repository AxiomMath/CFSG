
module

public import Certificates.Kernel.L34W.Tabs
public import Certificates.Kernel.L34W.Gens
public import CFSG.Certificates.Kernel.L34W.Tab42Sound

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem t1Of : T1Of T1X.F := t1Entry_of_hex T1X.eq T1X.all

theorem alOf : AlOf AlX.F := alphaEntry_of_hex AlX.eq AlX.all

theorem gensG : GensG GT := by
  have h := gens_k
  unfold gensOK at h
  rw [bAnd_iff] at h
  intro j hj
  have h2 := allN_spec h.2 j hj
  rw [bAnd_iff] at h2
  exact ⟨unpack_eq_of_bindArrK h2.1, h2.2⟩

theorem dec_mul {x y : ℕ} (hx : x < 1024) (hy : y < 1024) :
    dec (mulC T1X.F x y) = mulM (dec x) (dec y) := dec_mulC t1Of hx hy

theorem dec_inv {x : ℕ} (hx : x < 1024) : dec (invC T1X.F x) = invM (dec x) := dec_invC t1Of hx

theorem dec_beta {t i x : ℕ} (ht : t < 64) (hi : i < 36) (hx : x < 1024) :
    dec (betaC T1X.F AlX.F t i x) = betaYM t i (dec x) := dec_betaC t1Of alOf bounds_k ht hi hx

theorem yTab_eq (t : ℕ) {i : ℕ} (hi : i < 36) :
    Cn (yK GT t i) ∧ yTab t i = unpack 42 6 (yK GT t i) := yK_eq gensG t hi

end CertificateChecks.KernelL34W

end
