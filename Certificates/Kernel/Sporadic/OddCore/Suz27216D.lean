module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Data
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CertificateChecks.KernelSpor.N27216

open CFSG.EvenSporadicStandard.SuzN0 CFSG.PSL3Four.Native

meta def owM : Array (Array Nat) :=
  ((List.range 9).toArray.map oddTab).push zTab |>.push hTab

meta def gnM : Array (Array Nat) := gensN (invTab 1782 hTab)

meta def rgM : Array (Array Nat) := rTabs

meta def rgiM : Array (Array Nat) := rTabs.map (invTab 1782)

meta def idM : Array Nat := idTab 1782

end CertificateChecks.KernelSpor.N27216

#kmisc_packarrs CertificateChecks.KernelSpor.N27216.OW CertificateChecks.KernelSpor.N27216.owM 11
#kmisc_packarrs CertificateChecks.KernelSpor.N27216.GN CertificateChecks.KernelSpor.N27216.gnM 11
#kpenum CertificateChecks.KernelSpor.N27216.RE 1782 11 false CertificateChecks.KernelSpor.N27216.rgM
  CertificateChecks.KernelSpor.N27216.rgiM CertificateChecks.KernelSpor.N27216.idM 64

end
