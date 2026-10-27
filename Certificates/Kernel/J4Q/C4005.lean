module

public import CFSG.Sporadic.J4.QT2LocFixNative
public import Certificates.Kernel.J4Q.LocVec
public import Certificates.Kernel.J4Q.Orbits
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

theorem fix_of (s n : Nat) (ms : List Nat)
    (h : allR n (fun i => strictB (pathVK rm one [A, B] (repPaths.getD (s + 1 * i) []) (v2N rootV))
      fun v => ms.all fun c => neN (vecEtaK rm Us c v) v) = true) :
    ((List.range' s n).all fun l =>
      ms.all fun c => differs (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 c))
        (pathVec (repPaths.getD l []))) (pathVec (repPaths.getD l []))) = true := by
  refine List.all_eq_true.2 fun l hl => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hl
  have hk := allR_spec h i hi
  rw [strictB_eq] at hk
  obtain ⟨hw, hv⟩ := pathVec_enc (repPaths.getD (s + 1 * i) [])
  refine List.all_eq_true.2 fun c hc => ?_
  obtain ⟨hw2, hv2⟩ := etaVec_enc hw c
  rw [differs_eq hw2 hw, hv2, hv]
  exact List.all_eq_true.1 hk c hc

theorem fix2B_chk : allR 4 (fun i => strictB (pathVK rm one [A, B] (repPaths.getD (1 + 1 * i) [])
    (v2N rootV)) fun v => (fstsK (ptsK OR.s0)).all fun c => neN (vecEtaK rm Us c v) v) = true := by
  quickRfl

theorem fix2A_chk : allR 2 (fun i => strictB (pathVK rm one [A, B] (repPaths.getD (2 + 1 * i) [])
    (v2N rootV)) fun v => (fstsK (ptsK OR.s1)).all fun c => neN (vecEtaK rm Us c v) v) = true := by
  quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem c4005 : (chkFix2B = true)
    ∧ (chkFix2A = true) := by
  refine ⟨?_, ?_⟩
  · unfold chkFix2B
    simp only []
    rw [tMasks_eq]
    exact fix_of 1 4 _ fix2B_chk
  · unfold chkFix2A
    simp only []
    rw [zMasks_eq]
    exact fix_of 2 2 _ fix2A_chk

end CertificateChecks.KernelJ4Q

end
