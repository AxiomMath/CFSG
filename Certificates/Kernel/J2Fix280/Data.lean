module

public import Certificates.Data.J2Fix280
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.J2Fix280
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelJ2Fix280.Z 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr
#kmisc_packarrs CertificateChecks.KernelJ2Fix280.AB CFSG.ComponentClassification.J2Cover.autStrong 9
#ks_perm CertificateChecks.KernelJ2Fix280.TA 9 CFSG.RankThree.PartTwo.J2Residue.C280.tA
#ks_perm CertificateChecks.KernelJ2Fix280.TB 9 CFSG.RankThree.PartTwo.J2Residue.C280.tB
#ks_perm CertificateChecks.KernelJ2Fix280.TZ 9 CFSG.RankThree.PartTwo.J2Residue.C280.tZ
#ks_perm CertificateChecks.KernelJ2Fix280.REPS 9 CFSG.RankThree.PartTwo.J2Residue.C280.reps
#ks_perm CertificateChecks.KernelJ2Fix280.CLS 9 CFSG.RankThree.PartTwo.J2Residue.C280.cls
#ks_perm CertificateChecks.KernelJ2Fix280.UIDX 9 CFSG.RankThree.PartTwo.J2Residue.C280.uIdx

meta def ysArr : Array (Array Nat) :=
  Array.ofFn (n := 280) fun i => CFSG.RankThree.PartTwo.J2Residue.C280.conjY i.val

#kmisc_packarrs CertificateChecks.KernelJ2Fix280.YT ysArr 9
