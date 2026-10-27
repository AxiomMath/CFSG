
module

public import Certificates.Kernel.L34W.RealB
public import Certificates.Kernel.L34W.Glue
public import Certificates.Kernel.L34W.OutCov
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34W.RealBSound

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.L34W CFSG.KC.L34W.OCS CFSG.KC.L34W.RBS
open CFSG.KC.L34KSnd CFSG.KC.L34K CertificateChecks.KernelLC CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.KLie.CT (notB)

theorem invIdxOK_true : invIdxOK = true := invOKE_of t1Of ch22971g_inv

theorem parts {κ : ZMod 4 × ZMod 4} (hκ : κ ∈ kGensC) :
    ((List.range 36).all fun i => !liftsK κ i ||
      (List.range 64).all fun t => !fixBM κ t i || pow4M t i) = true ∧
    ((List.range 36).all fun i => repInS.contains i || !liftsK κ i ||
      (List.range 64).all fun t => !fixBM κ t i || allM.all fun w =>
        !eqKM κ (betaYM t i w) w ||
          !(allM.all fun x => eqKM κ (betaYM t i (betaYM t i x)) (mulM (mulM w x) (invM w))) ||
          trichM κ (allM.filter (isAhM κ)) t i w) = true := by
  simp only [kGensC, List.mem_cons, List.not_mem_nil, or_false] at hκ
  rcases hκ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cK_sound t1Of alOf bounds_k gensG y_k (k₁ := 1) (k₂ := 0) (by decide) (by decide +kernel)
      ch22220k_0
  · exact cK_sound t1Of alOf bounds_k gensG y_k (k₁ := 0) (k₂ := 1) (by decide) (by decide +kernel)
      ch22220k_1
  · exact cK_sound t1Of alOf bounds_k gensG y_k (k₁ := 1) (k₂ := 1) (by decide) (by decide +kernel)
      ch22220k_2
  · exact cK_sound t1Of alOf bounds_k gensG y_k (k₁ := 1) (k₂ := 2) (by decide) (by decide +kernel)
      ch22220k_3
  · exact cK_sound t1Of alOf bounds_k gensG y_k (k₁ := 2) (k₂ := 1) (by decide) (by decide +kernel)
      ch22220k_4
  · exact cK_sound t1Of alOf bounds_k gensG y_k (k₁ := 1) (k₂ := 3) (by decide) (by decide +kernel)
      ch22220k_5

theorem c2OK_true : c2OK = true := by
  unfold c2OK
  rw [Bool.and_eq_true, List.all_eq_true]
  exact ⟨invIdxOK_true, fun κ hκ => (parts hκ).1⟩

theorem c6OK_true : c6OK = true := by
  unfold c6OK
  rw [Bool.and_eq_true, List.all_eq_true]
  exact ⟨invIdxOK_true, fun κ hκ => (parts hκ).2⟩

theorem repS_found {i : ℕ} (hi : i < 36) (h : repSK GT L34S.T i = true) :
    found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T) (repTab i) = true := by
  unfold repSK at h
  rw [strictB_eq', notB_eq', Bool.not_eq_true'] at h
  rw [(repK_eq gensG hi).2]
  by_contra hne
  have h1 : ∀ q < 20160, notB (Nat.beq (L34S.T q) (repK GT i)) = true := by
    intro q hq
    rw [notB_eq', Bool.not_eq_true']
    cases hq' : Nat.beq (L34S.T q) (repK GT i)
    · rfl
    · exact absurd (by unfold pts; exact found_pts hq (Nat.eq_of_beq_eq_true hq')) hne
  exact absurd ((allN_iff'.2 h1).symm.trans h) (by decide)

theorem repSOK_true : repSOK = true := by
  unfold repSOK
  dsimp only
  rw [L34Cert.hS.1, List.all_eq_true]
  intro i hi
  simp only [repInS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact repS_found (by norm_num) ch22220s_0
  · exact repS_found (by norm_num) ch22220s_25
  · exact repS_found (by norm_num) ch22220s_31

theorem realBOK_true : realBOK = true := by
  unfold realBOK
  rw [c2OK_true, c6OK_true, repSOK_true]
  rfl

end CertificateChecks.KernelL34W

end
