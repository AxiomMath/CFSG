module

public import Certificates.Kernel.Sporadic.SuzI301K.GlueInv

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KC.LinRepSound CFSG.KC.LinRepCheck CFSG.KC.SuzI301Lin
open CFSG.KC.SuzI301K CFSG.KD.SuzI301 CFSG.PSL3Four.Native CFSG.Sporadic.SuzI301
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin CertificateChecks.KernelLC

theorem fix_facts : allBelow 128 (fun j => comm1782 (sD ()) qElts[j]! ==
    ((mat64 (sD ()))[j / 2]! == j / 2)) = true := by
  rw [mat64_cw_D, d_eq]
  refine allBelow_true fun j hj => ?_
  have hv : j / 2 < 64 := by omega
  rw [qe_eq hj, comm_eq pD (permB_of_pp (pQE hj)), linTab_get _ hv, ← appW_eq_ev]
  have e := CFSG.KS.allN_spec kFix j hj
  beta_reduce at e
  rw [strictB_eq', CFSG.KC.B0SuzK.shiftRight_one_eq] at e
  cases hc : commP (SuzHS.F 1) (SuzB0QE j)
  · rw [hc] at e
    change nB (Nat.beq (appW (nthN CW 0) (j / 2)) (j / 2)) = true at e
    rw [nB_eq] at e
    cases hb : Nat.beq (appW (nthN CW 0) (j / 2)) (j / 2)
    · have hne : appW (nthN CW 0) (j / 2) ≠ j / 2 := fun h => by
        rw [h, Nat.beq_refl] at hb
        exact absurd hb (by decide)
      simp [hne]
    · rw [hb] at e
      exact absurd e (by decide)
  · rw [hc] at e
    change Nat.beq (appW (nthN CW 0) (j / 2)) (j / 2) = true at e
    have heq := Nat.eq_of_beq_eq_true e
    simp [heq]

end CertificateChecks.KernelSpor.SuzI301K

end
