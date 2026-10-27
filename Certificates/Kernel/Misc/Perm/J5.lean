module

public import Certificates.Kernel.Misc.Perm.J5T0
public import Certificates.Kernel.Misc.Perm.J5T1
public import Certificates.Kernel.Misc.Perm.J5T2
public import Certificates.Kernel.Misc.Perm.J5T3
public import Certificates.Kernel.Misc.Perm.J5T4
public import Certificates.Kernel.Misc.Perm.J5T5
public import Certificates.Kernel.Misc.Perm.J5W0
public import Certificates.Kernel.Misc.Perm.J5W1
public import Certificates.Kernel.Misc.Perm.J5W4
public import Certificates.Kernel.Misc.Perm.J5D2
public import Certificates.Kernel.Misc.Perm.J5D3
public import Certificates.Kernel.Misc.Perm.J5D5

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.RankThree.PartOne

theorem centCheck {i N : ℕ} (hc : caseChainOK3 315 (j2FiveRS i)
      ((j2FiveRBase i).map Fin.val).toArray (j2FiveRW i) j2FiveGensR[0]! j2FiveGensR[1]!
      j2FiveGensR[2]! = true)
    (ht : centOKP 5 315 (j2FiveRS i) ((j2FiveRBase i).map Fin.val).toArray (j2FiveX i)
      (j2FiveRRels i) (j2FiveCG i) j2FiveKeyPts (j2FiveCCert i) N = true) :
    j2FiveCentCheck i N = true := by
  rw [j2FiveCentCheck, hc, ht]
  rfl

open Certificates in
open CFSG.RankThree.Native CFSG.RankThree.PartOne in
theorem facts :
    ((List.range 3).all (fun k => validA 315 j2FiveGensR[k]!) = true)
    ∧ (j2FiveQCheck j2FiveQCert = true)
    ∧ (j2FiveCentCheck 0 50 = true)
    ∧ (j2FiveCentCheck 1 50 = true)
    ∧ (j2FiveCentCheck 2 300 = true)
    ∧ (j2FiveCentCheck 3 300 = true)
    ∧ (j2FiveCentCheck 4 50 = true)
    ∧ (j2FiveCentCheck 5 300 = true)
    ∧ (j2FiveGoodCheck 0 (j2FiveCCert 0) j2FiveQCert = true)
    ∧ (j2FiveGoodCheck 1 (j2FiveCCert 1) j2FiveQCert = true)
    ∧ (j2FiveGoodCheck 4 (j2FiveCCert 4) j2FiveQCert = true)
    ∧ (j2FiveBadCheck 2 (j2FiveCCert 2) (j2FiveDCert 2) j2FiveQCert = true)
    ∧ (j2FiveBadCheck 3 (j2FiveCCert 3) (j2FiveDCert 3) j2FiveQCert = true)
    ∧ (j2FiveBadCheck 5 (j2FiveCCert 5) (j2FiveDCert 5) j2FiveQCert = true) :=
  ⟨gensValid, qCheck, centCheck chain0 cent0, centCheck chain1 cent1, centCheck chain2 cent2,
    centCheck chain3 cent3, centCheck chain4 cent4, centCheck chain5 cent5, good0, good1, good4,
    bad2, bad3, bad5⟩

end CertificateChecks.KernelMisc.J2F

end
