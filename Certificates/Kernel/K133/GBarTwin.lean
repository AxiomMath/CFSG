module

public import Certificates.Kernel.K133.GBarData
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelK133.GBarE

meta def gbTwRows : Array (Array Nat) :=
  ((include_str "GBarTwin.txt").splitOn "\n").toArray.map fun l =>
    ((l.splitOn " ").filterMap String.toNat?).toArray

meta def gbTwPerms (r : Nat) : Array (Array Nat) :=
  let a := gbTwRows[r]!
  (Array.range (a.size / 256)).map fun k => a.extract (256 * k) (256 * k + 256)

meta def fiL : List Nat := gbTwRows[0]!.toList
meta def wiL : List Nat := gbTwRows[1]!.toList
meta def p5L : List Nat := gbTwRows[2]!.toList
meta def p2L : List Nat := gbTwRows[3]!.toList
meta def q5L : List Nat := gbTwRows[4]!.toList
meta def q2L : List Nat := gbTwRows[5]!.toList
meta def l2M : Array (Array Nat) := gbTwPerms 6
meta def l3M : Array (Array Nat) := gbTwPerms 7
meta def l4M : Array (Array Nat) := gbTwPerms 8
meta def uvL : List Nat := gbTwRows[9]!.toList
meta def uoL : List Nat := gbTwRows[10]!.toList

end CertificateChecks.KernelK133.GBarE

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelK133.GB.FI CertificateChecks.KernelK133.GBarE.fiL
#kss_natlist CertificateChecks.KernelK133.GB.WI CertificateChecks.KernelK133.GBarE.wiL
#kss_natlist CertificateChecks.KernelK133.GB.P5 CertificateChecks.KernelK133.GBarE.p5L
#kss_natlist CertificateChecks.KernelK133.GB.P2 CertificateChecks.KernelK133.GBarE.p2L
#kss_natlist CertificateChecks.KernelK133.GB.Q5 CertificateChecks.KernelK133.GBarE.q5L
#kss_natlist CertificateChecks.KernelK133.GB.Q2 CertificateChecks.KernelK133.GBarE.q2L
#kmisc_packarrs CertificateChecks.KernelK133.GB.L2 CertificateChecks.KernelK133.GBarE.l2M 9
#kmisc_packarrs CertificateChecks.KernelK133.GB.L3 CertificateChecks.KernelK133.GBarE.l3M 9
#kmisc_packarrs CertificateChecks.KernelK133.GB.L4 CertificateChecks.KernelK133.GBarE.l4M 9
#kss_natlist CertificateChecks.KernelK133.GB.UV CertificateChecks.KernelK133.GBarE.uvL
#kss_natlist CertificateChecks.KernelK133.GB.UO CertificateChecks.KernelK133.GBarE.uoL

end
