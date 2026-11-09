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

meta def mclLwM : Array Nat := Id.run do
  let mut r := Array.replicate (32 * lettersM.size) 0
  for l in [0:lettersM.size] do
    let t := lettersM[l]!
    let mut v := l + 1
    for x in [0:t.size] do
      v := v ||| (t[x]!.toNat <<< (16 * (x + 1)))
    r := r.set! (32 * l) v
  return r

meta def lv0M : Array Nat := levelLetters lettersM chainBase 0
meta def lv1M : Array Nat := levelLetters lettersM chainBase 1
meta def lv2M : Array Nat := levelLetters lettersM chainBase 2
meta def lv3M : Array Nat := levelLetters lettersM chainBase 3
meta def lv4M : Array Nat := levelLetters lettersM chainBase 4
meta def lv5M : Array Nat := levelLetters lettersM chainBase 5

meta def mclGLM : Array Nat := #[0, 0, 0, 0, 0, 1, 4, 3, 4, 5, 6, 3, 10, 11, 9, 14, 1, 16, 5, 2, 4, 15,
  2, 18, 5, 1, 6, 24, 27, 28, 29, 30, 18, 22, 33, 34, 35, 36, 37, 21, 11, 5, 38, 41, 42, 40, 24, 6, 46,
  42, 49, 50, 51, 52, 53, 54, 3, 2, 2, 9, 59, 60, 61, 62, 63, 41, 65, 64, 4, 66, 19, 5, 37, 56, 8, 74,
  75, 76, 77, 78, 79, 56, 81, 82, 83, 84, 85, 86, 87, 80, 89, 43, 88, 38, 93, 1, 66, 96, 2, 9, 99, 100,
  101, 102, 103, 104, 105, 106, 107, 108, 92, 110, 111, 112, 113, 114, 115, 116, 91, 118, 119, 120,
  121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 7, 133, 134, 135, 136, 137, 138, 109, 25, 117,
  132, 139, 80, 19, 25, 140, 10, 109, 38, 55, 141, 98, 14, 139, 71, 32, 20, 143, 145, 147, 149, 151,
  153, 155, 157, 159, 160, 162, 164, 166, 169, 171, 173, 175]
meta def mclGRM : Array Nat := #[0, 0, 0, 0, 0, 3, 2, 3, 4, 7, 8, 5, 4, 2, 13, 6, 12, 6, 17, 8, 1, 7, 3,
  6, 21, 1, 2, 25, 9, 1, 20, 20, 10, 22, 19, 26, 19, 32, 23, 31, 39, 15, 4, 40, 23, 1, 31, 7, 1, 43, 5,
  48, 43, 25, 8, 47, 1, 2, 38, 57, 44, 58, 6, 44, 45, 2, 55, 23, 67, 56, 68, 2, 18, 8, 68, 70, 7, 45,
  47, 2, 4, 5, 73, 71, 72, 12, 69, 66, 3, 26, 4, 90, 44, 12, 67, 5, 11, 46, 42, 17, 26, 72, 7, 13, 26,
  55, 11, 48, 23, 70, 88, 94, 98, 41, 6, 94, 10, 1, 69, 41, 58, 12, 64, 5, 16, 39, 95, 14, 8, 6, 26,
  57, 7, 5, 97, 5, 23, 45, 97, 90, 92, 95, 6, 71, 43, 6, 20, 5, 117, 141, 88, 6, 73, 140, 5, 2, 91, 37,
  71, 6, 144, 146, 148, 150, 152, 154, 156, 158, 3, 161, 163, 165, 167, 170, 172, 174, 168]
meta def mclRoM : Array Nat := #[2, 4, 23, 45, 69, 91, 142, 132, 176]

meta def symTabsM : Array (Array Nat) := Id.run do
  let mut ts : Array (Array Nat) := #[biM, alM, alM, biM, beM]
  for s in [5:mclGLM.size] do
    let l := ts[mclGLM[s]!]!
    ts := ts.push (ts[mclGRM[s]!]!.map fun y => l[y]!)
  return ts

meta def mclRtM : Array Nat := symTabsM.flatten

end CertificateChecks.KernelSpor.McLK

#krows CertificateChecks.KernelSpor.McLK.MclGL CertificateChecks.KernelSpor.McLK.mclGLM
#krows CertificateChecks.KernelSpor.McLK.MclGR CertificateChecks.KernelSpor.McLK.mclGRM
#krows CertificateChecks.KernelSpor.McLK.MclRO CertificateChecks.KernelSpor.McLK.mclRoM
#krowsw CertificateChecks.KernelSpor.McLK.MclRT 16 CertificateChecks.KernelSpor.McLK.mclRtM

#krowsw CertificateChecks.KernelSpor.McLK.PT 64 CertificateChecks.KernelSpor.McLK.ptM
#krows CertificateChecks.KernelSpor.McLK.AL CertificateChecks.KernelSpor.McLK.alM
#krows CertificateChecks.KernelSpor.McLK.BE CertificateChecks.KernelSpor.McLK.beM
#krows CertificateChecks.KernelSpor.McLK.PA CertificateChecks.KernelSpor.McLK.paM
#krows CertificateChecks.KernelSpor.McLK.LA CertificateChecks.KernelSpor.McLK.laM
#krows CertificateChecks.KernelSpor.McLK.BI CertificateChecks.KernelSpor.McLK.biM
#krows CertificateChecks.KernelSpor.McLK.SO CertificateChecks.KernelSpor.McLK.soM
#krowsw CertificateChecks.KernelSpor.McLK.MclLW 4416 CertificateChecks.KernelSpor.McLK.mclLwM

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
