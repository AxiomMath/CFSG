module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SuzRecog.B0GluingTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.Sporadic.SuzRecog.B0Gluing

meta def mR : Array (Array Nat) := mulI
meta def cR : Array (Array Nat) := cmI
meta def iR : Array (Array Nat) := #[invI]
meta def xR : Array (Array Nat) := chiIs
meta def gR : Array (Array Nat) := gammaIs
meta def giR : Array (Array Nat) := gammaInvIs
meta def pR : Array (Array Nat) := thetaPerms
meta def piR : Array (Array Nat) := thetaInvPerms
meta def aR : Array (Array Nat) := nActs
meta def kR : Array (Array Nat) := cActs
meta def rT : Array (Array Nat) := rtabs
meta def tT : Array (Array Nat) := Array.ofFn (n := 36) fun i => thetaTab i.val
meta def tiT : Array (Array Nat) := Array.ofFn (n := 36) fun i => thetaInvTab i.val
meta def nT : Array (Array Nat) := nTabs
meta def niT : Array (Array Nat) := nInvs
meta def wT : Array (Array Nat) := cTabsW
meta def wiT : Array (Array Nat) := cInvsW
meta def yT : Array (Array Nat) := y0Tabs[0]! ++ y0Tabs[1]!

end CertificateChecks.KernelSpor.SuzGl

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlM CertificateChecks.KernelSpor.SuzGl.mR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlC CertificateChecks.KernelSpor.SuzGl.cR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlI CertificateChecks.KernelSpor.SuzGl.iR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlX CertificateChecks.KernelSpor.SuzGl.xR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlG CertificateChecks.KernelSpor.SuzGl.gR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlGI CertificateChecks.KernelSpor.SuzGl.giR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlP CertificateChecks.KernelSpor.SuzGl.pR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlPI CertificateChecks.KernelSpor.SuzGl.piR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlA CertificateChecks.KernelSpor.SuzGl.aR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlK CertificateChecks.KernelSpor.SuzGl.kR 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlR CertificateChecks.KernelSpor.SuzGl.rT 6
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlT CertificateChecks.KernelSpor.SuzGl.tT 6
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlTI CertificateChecks.KernelSpor.SuzGl.tiT 6
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlN CertificateChecks.KernelSpor.SuzGl.nT 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlNI CertificateChecks.KernelSpor.SuzGl.niT 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlW CertificateChecks.KernelSpor.SuzGl.wT 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlWI CertificateChecks.KernelSpor.SuzGl.wiT 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGlY CertificateChecks.KernelSpor.SuzGl.yT 11

end
