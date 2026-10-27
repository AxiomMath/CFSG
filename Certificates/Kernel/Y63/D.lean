module

public import Certificates.Data.Y63.Check
meta import Certificates.Data.Y63.Check
public import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

meta def tM : Array (Array Nat) := tabRows ()
meta def wM : Array (Array Nat) :=
  (bfsWords (tabRows ()) ()).map fun w => #[w.length] ++ w.toArray
meta def mtM : Array (Array Nat) := mulTable (tabRows ()) (bfsWords (tabRows ()) ()) ()
meta def ivM : Array (Array Nat) :=
  #[invTable (mulTable (tabRows ()) (bfsWords (tabRows ()) ()) ()) ()]
meta def tauM : Array (Array Nat) := tauData ()
meta def skM : Array (Array Nat) := (skData ()).map List.toArray
meta def u0M : Array (Array Nat) := (u0Data ()).map List.toArray
meta def m0M : Array (Array Nat) := #[(m0Data ()).toArray, (repsData ()).toArray]
meta def cjM : Array (Array Nat) :=
  #[((cjData ()).map fun e => [e.1, e.2.1, e.2.2.1, e.2.2.2]).flatten.toArray]
meta def cwM : Array (Array Nat) :=
  (cwData ()).map fun l => (l.map fun e => [e.1, e.2.1, e.2.2.1, e.2.2.2]).flatten.toArray
meta def lnM : Array (Array Nat) :=
  #[#[(repsData ()).length, (cjData ()).length] ++ (cwData ()).map List.length]

end CertificateChecks.KernelY63

#kmisc_packarrs CertificateChecks.KernelY63.TT CertificateChecks.KernelY63.tM 9
#kmisc_packarrs CertificateChecks.KernelY63.WT CertificateChecks.KernelY63.wM 9
#kmisc_packarrs CertificateChecks.KernelY63.MT CertificateChecks.KernelY63.mtM 9
#kmisc_packarrs CertificateChecks.KernelY63.IVT CertificateChecks.KernelY63.ivM 9
#kmisc_packarrs CertificateChecks.KernelY63.TAUT CertificateChecks.KernelY63.tauM 9
#kmisc_packarrs CertificateChecks.KernelY63.SKT CertificateChecks.KernelY63.skM 9
#kmisc_packarrs CertificateChecks.KernelY63.U0T CertificateChecks.KernelY63.u0M 10
#kmisc_packarrs CertificateChecks.KernelY63.M0T CertificateChecks.KernelY63.m0M 9
#kmisc_packarrs CertificateChecks.KernelY63.CJT CertificateChecks.KernelY63.cjM 9
#kmisc_packarrs CertificateChecks.KernelY63.CWT CertificateChecks.KernelY63.cwM 10
#kmisc_packarrs CertificateChecks.KernelY63.LNT CertificateChecks.KernelY63.lnM 16

end
