module

public import Certificates.Data.NT44Model.Inputs
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.NT44Model.Inputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.Monster.B.Co2.Native

meta def ksM : Array (Array Nat) := ks ()
meta def p0M : Array (Array Nat) := p0 ()
meta def liftsM : Array (Array Nat) := lifts ()
meta def ksiM : Array (Array Nat) := (ks ()).map (invCand 2688)
meta def p0iM : Array (Array Nat) := (p0 ()).map (invCand 2688)
meta def liftsiM : Array (Array Nat) := (lifts ()).map (invCand 2688)
meta def skM : Array (Array Nat) := sk ()
meta def spM : Array (Array Nat) := sp ()

end CertificateChecks.KernelNT44

end

#kmisc_packarrs CertificateChecks.KernelNT44.nt44KS CertificateChecks.KernelNT44.ksM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44P0 CertificateChecks.KernelNT44.p0M 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44L CertificateChecks.KernelNT44.liftsM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44KSI CertificateChecks.KernelNT44.ksiM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44P0I CertificateChecks.KernelNT44.p0iM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44LI CertificateChecks.KernelNT44.liftsiM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44SK CertificateChecks.KernelNT44.skM 9
#kmisc_packarrs CertificateChecks.KernelNT44.nt44SP CertificateChecks.KernelNT44.spM 9
