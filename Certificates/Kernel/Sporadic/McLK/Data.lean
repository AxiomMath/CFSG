module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.CFSGNative.McL.Certificate
public meta import Certificates.Data.CFSGNative.McL.Certificate

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.McLSeedA CFSG.Sporadic.McL.Native.seedA
#ks_chars CertificateChecks.KernelSpor.McLSeedB CFSG.Sporadic.McL.Native.seedB

namespace CertificateChecks.KernelSpor.McLK

open CFSG.Sporadic.McL.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.VecOrbit.Native

meta def orbM : VOrbit := orbitData ()

meta def ptM : Array Nat := orbM.pts.map fun v => v.p + 2 ^ 32 * v.m

meta def alM : Array Nat := orbM.alpha.map (·.toNat)
meta def beM : Array Nat := orbM.beta.map (·.toNat)
meta def paM : Array Nat := orbM.par.map (·.toNat)
meta def laM : Array Nat := orbM.lab.map (·.toNat)

meta def biM : Array Nat := Id.run do
  let mut r := Array.replicate 275 0
  for i in [0:275] do
    r := r.set! beM[i]! i
  return r

meta def soM : Array Nat := ((List.range 275).toArray.qsort fun i j => ptM[i]! < ptM[j]!)

meta def lettersM : Array Table := chainLetters orbM

meta def ltM : Array Nat := (lettersM.map fun t => t.map (·.toNat)).flatten

meta def lv0M : Array Nat := levelLetters lettersM chainBase 0
meta def lv1M : Array Nat := levelLetters lettersM chainBase 1
meta def lv2M : Array Nat := levelLetters lettersM chainBase 2
meta def lv3M : Array Nat := levelLetters lettersM chainBase 3
meta def lv4M : Array Nat := levelLetters lettersM chainBase 4
meta def lv5M : Array Nat := levelLetters lettersM chainBase 5

meta def codeZM (z : Int) : Nat :=
  match z with
  | .ofNat k => 2 * k
  | .negSucc k => 2 * k + 1

meta def wM (j : Nat) : List Nat := ((chainWords ())[j]!).map codeZM
meta def w0M : List Nat := wM 0
meta def w1M : List Nat := wM 1
meta def w2M : List Nat := wM 2
meta def w3M : List Nat := wM 3
meta def w4M : List Nat := wM 4
meta def w5M : List Nat := wM 5
meta def w6M : List Nat := wM 6
meta def w7M : List Nat := wM 7
meta def w8M : List Nat := wM 8

end CertificateChecks.KernelSpor.McLK

#knatlist CertificateChecks.KernelSpor.McLK.W0 CertificateChecks.KernelSpor.McLK.w0M
#knatlist CertificateChecks.KernelSpor.McLK.W1 CertificateChecks.KernelSpor.McLK.w1M
#knatlist CertificateChecks.KernelSpor.McLK.W2 CertificateChecks.KernelSpor.McLK.w2M
#knatlist CertificateChecks.KernelSpor.McLK.W3 CertificateChecks.KernelSpor.McLK.w3M
#knatlist CertificateChecks.KernelSpor.McLK.W4 CertificateChecks.KernelSpor.McLK.w4M
#knatlist CertificateChecks.KernelSpor.McLK.W5 CertificateChecks.KernelSpor.McLK.w5M
#knatlist CertificateChecks.KernelSpor.McLK.W6 CertificateChecks.KernelSpor.McLK.w6M
#knatlist CertificateChecks.KernelSpor.McLK.W7 CertificateChecks.KernelSpor.McLK.w7M
#knatlist CertificateChecks.KernelSpor.McLK.W8 CertificateChecks.KernelSpor.McLK.w8M

#krowsw CertificateChecks.KernelSpor.McLK.PT 64 CertificateChecks.KernelSpor.McLK.ptM
#krows CertificateChecks.KernelSpor.McLK.AL CertificateChecks.KernelSpor.McLK.alM
#krows CertificateChecks.KernelSpor.McLK.BE CertificateChecks.KernelSpor.McLK.beM
#krows CertificateChecks.KernelSpor.McLK.PA CertificateChecks.KernelSpor.McLK.paM
#krows CertificateChecks.KernelSpor.McLK.LA CertificateChecks.KernelSpor.McLK.laM
#krows CertificateChecks.KernelSpor.McLK.BI CertificateChecks.KernelSpor.McLK.biM
#krows CertificateChecks.KernelSpor.McLK.SO CertificateChecks.KernelSpor.McLK.soM
#krows CertificateChecks.KernelSpor.McLK.LT CertificateChecks.KernelSpor.McLK.ltM

#ktbfs CertificateChecks.KernelSpor.McLK.CT0 275 0 CertificateChecks.KernelSpor.McLK.lettersM
  CertificateChecks.KernelSpor.McLK.lv0M
#ktbfs CertificateChecks.KernelSpor.McLK.CT1 275 1 CertificateChecks.KernelSpor.McLK.lettersM
  CertificateChecks.KernelSpor.McLK.lv1M
#ktbfs CertificateChecks.KernelSpor.McLK.CT2 275 2 CertificateChecks.KernelSpor.McLK.lettersM
  CertificateChecks.KernelSpor.McLK.lv2M
#ktbfs CertificateChecks.KernelSpor.McLK.CT3 275 3 CertificateChecks.KernelSpor.McLK.lettersM
  CertificateChecks.KernelSpor.McLK.lv3M
#ktbfs CertificateChecks.KernelSpor.McLK.CT4 275 4 CertificateChecks.KernelSpor.McLK.lettersM
  CertificateChecks.KernelSpor.McLK.lv4M
#ktbfs CertificateChecks.KernelSpor.McLK.CT5 275 5 CertificateChecks.KernelSpor.McLK.lettersM
  CertificateChecks.KernelSpor.McLK.lv5M
#ktbfs CertificateChecks.KernelSpor.McLK.T2 275 2 CertificateChecks.KernelSpor.McLK.lettersM
  CertificateChecks.KernelSpor.McLK.lv1M

end
