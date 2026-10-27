module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3C

open CFSG.ClassicalInvolution.J3Data CFSG.Perm.Native CFSG.Sporadic.Th.Native
  CFSG.Monster.B.Co2.Native

meta def tabM (t : Array Nat) : Table := t.map UInt32.ofNat

meta def kLetM : Array Table := #[tabM kStrong[0]!, tabM kInv[0]!, tabM kStrong[1]!, tabM kInv[1]!]

meta def uLetM : Array Table := uStrong.map tabM
meta def sLetM : Array Table := sStrong.map tabM

meta def lv4M : Array Nat := #[0, 1, 2, 3]

meta def klM : Array Nat := kStrong[0]! ++ kInv[0]! ++ kStrong[1]! ++ kInv[1]!

meta def ciM : Array Nat :=
  let T := treeBFS 20520 0 sLetM lv4M
  let ys := conjInvols.map fun c => c[0]!
  T.pts.map fun p => ys.idxOf p.toNat % ys.length

end CertificateChecks.KernelSpor.J3C

#krows CertificateChecks.KernelSpor.J3C.KL CertificateChecks.KernelSpor.J3C.klM
#krows CertificateChecks.KernelSpor.J3C.CI CertificateChecks.KernelSpor.J3C.ciM

#ktbfs CertificateChecks.KernelSpor.J3C.TK 20520 0 CertificateChecks.KernelSpor.J3C.kLetM
  CertificateChecks.KernelSpor.J3C.lv4M
#ktbfs CertificateChecks.KernelSpor.J3C.TU 20520 0 CertificateChecks.KernelSpor.J3C.uLetM
  CertificateChecks.KernelSpor.J3C.lv4M
#ktbfs CertificateChecks.KernelSpor.J3C.TS 20520 0 CertificateChecks.KernelSpor.J3C.sLetM
  CertificateChecks.KernelSpor.J3C.lv4M

end
