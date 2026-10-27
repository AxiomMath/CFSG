module

public import CFSG.Certificates.Kernel.Fi22RkInv.Sound
public import Certificates.Kernel.Fi22RkInv.Checks
public import Certificates.Kernel.Fi22Gen.Glue
public import Certificates.Kernel.Fi22Reps.Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBMCover

public section

namespace CertificateChecks.KernelFi22RkInv

open CFSG.KS.Fi22RkInv CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three

theorem xRep_acts {k : Nat} (hk : k < 4) : ActsAs (xRep k) (xP k) := fun y hy =>
  ((CFSG.KD.Fi22Reps.repE_iff.1 (CertificateChecks.KernelFi22Reps.rep_xT hk) y hy).trans
    (CFSG.Sporadic.Th.idx_of_lt _ hy)).symm

theorem invRep_ok {k : Nat} (hk : k < 4) : invRep k = true := by
  interval_cases k
  · exact ch17373inv0
  · exact ch17373inv1
  · exact ch17373inv2
  · exact ch17373inv3


theorem rkBMInvAt_xRep {k : Nat} (hk : k < 4) :
    CFSG.HardMathSupport.Dickson.I271.RkBMInvAt (xRep k) :=
  invK_sound _ CertificateChecks.KernelFi22Gen.letters_act (xRep_acts hk)
    CertificateChecks.KernelFi22Gen.sep5 (invRep_ok hk)

end CertificateChecks.KernelFi22RkInv

end
