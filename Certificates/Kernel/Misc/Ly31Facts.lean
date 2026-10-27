module

public import Certificates.Kernel.Misc.LyDihFacts
public import Certificates.Kernel.Misc.Ly31Checks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy31

open CFSG.KC.Ord CFSG.KD.OrdLy CFSG.KS.SporSch.LyM CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelLyDih

local notation "U" X:max => unpackL 111 12 1332 X

theorem ly31Check_true : ly31Check () = true := by
  have hC : ly31C () = U CW := (wordE ly31Word).1
  have vC : vld CW = true := (wordE ly31Word).2
  have hCi : ly31Ci () = U CWi := (wordE ly31WordInv).1
  have vCi : vld CWi = true := (wordE ly31WordInv).2
  have hP : ly31P () = U PK := by
    unfold ly31P PK
    rw [show ly31C () = U CW from hC, show ly31Ci () = U CWi from hCi, matA_eq,
      mulE vC vA, mulE (mulV vC vA) vCi, mulE vA (mulV (mulV vC vA) vCi)]
  have vP : vld PK = true := mulV vA (mulV (mulV vC vA) vCi)
  have h := ok31
  unfold ly31Check
  rw [show ly31C () = U CW from hC, show ly31Ci () = U CWi from hCi, hP, mulE vC vCi, idE,
    beqE (mulV vC vCi) vOne, (powM_eq consts (hv vP) 31).1,
    beqE (powM_eq consts (hv vP) 31).2 vOne, diffMod5_eq consts (hv vP) (hv vOne)]
  exact h

end CertificateChecks.KernelLy31

end
