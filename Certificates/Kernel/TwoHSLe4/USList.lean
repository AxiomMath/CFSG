module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUCheck
public import Certificates.Kernel.TwoHSLe4.RawB
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
public import CFSG.Certificates.Kernel.Common.Harness
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CertificateChecks.KernelTwoHSLe4

open CFSG.EvenSporadicStandard.TwoHS

theorem omList_two : ∀ v ∈ omList, v + v = 0 := by decide +kernel

@[expose] def lamF (sr : List R4) : Bool :=
  allR (fun b => allV (fun u => memV (rmv b u) fR) fR) sr

theorem rmv_radd (b : R4) (v : RV) : radd (rmv b v) (rmv b v) = rmv b (radd v v) :=
  ofRV_inj (wf_radd _ _) (wf_rmv _ _)
    (by rw [ofRV_radd, ofRV_rmv, ofRV_rmv, ofRV_radd, Matrix.mulVec_add])

theorem uLamCheck_of_lamF {sr : List R4} (h : lamF sr = true) : uLamCheck sr = true := by
  simp only [uLamCheck, List.all_eq_true]
  intro b hb v _
  rw [Bool.or_eq_true]
  by_cases hv : inFR (radd v v) = true
  · right
    unfold inFR at hv ⊢
    rw [List.contains_iff_mem] at hv ⊢
    rw [rmv_radd]
    exact memV_iff.1 (allV_iff.1 (allR_iff.1 h b hb) _ hv)
  · left
    simpa using hv

theorem uSCheck_of {a : R4} (h1 : lamF (sListR a) = true) (h2 : uKerCheck (sListR a) = true)
    (h3 : uFxCheck (sListR a) = true) : uSCheck a = true := by
  rw [uSCheck, uLamCheck_of_lamF h1, h2, h3]
  rfl

set_option maxHeartbeats 0 in
theorem lamF_alpha1 : lamF (sListR (toR4 alpha1)) = true := by quickRfl

set_option maxHeartbeats 0 in
theorem uKerCheck_alpha1 : uKerCheck (sListR (toR4 alpha1)) = true := by quickRfl

set_option maxHeartbeats 0 in
theorem uFxCheck_alpha1 : uFxCheck (sListR (toR4 alpha1)) = true := by quickRfl

set_option maxHeartbeats 0 in
theorem lamF_alpha2 : lamF (sListR (toR4 alpha2)) = true := by quickRfl

set_option maxHeartbeats 0 in
theorem uKerCheck_alpha2 : uKerCheck (sListR (toR4 alpha2)) = true := by quickRfl

set_option maxHeartbeats 0 in
theorem uFxCheck_alpha2 : uFxCheck (sListR (toR4 alpha2)) = true := by quickRfl

theorem uSCheck_alpha1 : uSCheck (toR4 alpha1) = true :=
  uSCheck_of lamF_alpha1 uKerCheck_alpha1 uFxCheck_alpha1

theorem uSCheck_alpha2 : uSCheck (toR4 alpha2) = true :=
  uSCheck_of lamF_alpha2 uKerCheck_alpha2 uFxCheck_alpha2

end CertificateChecks.KernelTwoHSLe4
