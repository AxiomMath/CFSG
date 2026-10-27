module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Data.CFSGNative.J2.Certificate
public meta import Certificates.Data.CFSGNative.J2.Certificate

public section

namespace CertificateChecks.KernelSpor.J2K

open CFSG.Sporadic.J2.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.J1.Native (Orb PrimData primData)

meta def orbM : Orb := orbitData ()

meta def codeM (v : List Nat) : Nat := (v.zipIdx.map fun (x, k) => x <<< (4 * k)).foldl (· ||| ·) 0

meta def ptM : Array Nat := orbM.pts.map codeM

meta def alM : Array Nat := orbM.alpha.map (·.toNat)
meta def beM : Array Nat := orbM.beta.map (·.toNat)
meta def paM : Array Nat := orbM.par
meta def laM : Array Nat := orbM.lab

meta def invM (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 315 0
  for i in [0:315] do
    r := r.set! t[i]! i
  return r

meta def aiM : Array Nat := invM alM
meta def biM : Array Nat := invM beM

meta def soM : Array Nat := ((List.range 315).toArray.qsort fun i j => ptM[i]! < ptM[j]!)

meta def lettersM : Array Table := chainLetters orbM

meta def ltM : Array Nat := (lettersM.map fun t => t.map (·.toNat)).flatten

meta def lv0M : Array Nat := levelLetters lettersM chainBase 0
meta def lv1M : Array Nat := levelLetters lettersM chainBase 1
meta def lv2M : Array Nat := levelLetters lettersM chainBase 2

meta def t0M : Tree := (chainTrees 315 lettersM chainBase)[0]!

meta def primM : PrimData := primData 315 lettersM lv1M t0M

meta def lblM : Array Nat := primM.lab
meta def repM : Array Nat := primM.reps
meta def imM : Array Nat := primM.imgs.flatten

meta def dsM : Array Nat := (primM.ders.map fun l => (l.map fun s => s.1 * 65536 + s.2).toArray).flatten

meta def doffM : Array Nat :=
  ((List.range primM.ders.size).map fun i =>
    ((primM.ders.toList.take i).map List.length).sum).toArray

meta def dlenM : Array Nat := primM.ders.map List.length

end CertificateChecks.KernelSpor.J2K

#krowsw CertificateChecks.KernelSpor.J2K.PT 64 CertificateChecks.KernelSpor.J2K.ptM
#krows CertificateChecks.KernelSpor.J2K.AL CertificateChecks.KernelSpor.J2K.alM
#krows CertificateChecks.KernelSpor.J2K.BE CertificateChecks.KernelSpor.J2K.beM
#krows CertificateChecks.KernelSpor.J2K.PA CertificateChecks.KernelSpor.J2K.paM
#krows CertificateChecks.KernelSpor.J2K.LA CertificateChecks.KernelSpor.J2K.laM
#krows CertificateChecks.KernelSpor.J2K.AI CertificateChecks.KernelSpor.J2K.aiM
#krows CertificateChecks.KernelSpor.J2K.BI CertificateChecks.KernelSpor.J2K.biM
#krows CertificateChecks.KernelSpor.J2K.SO CertificateChecks.KernelSpor.J2K.soM
#krows CertificateChecks.KernelSpor.J2K.LT CertificateChecks.KernelSpor.J2K.ltM
#krows CertificateChecks.KernelSpor.J2K.LBL CertificateChecks.KernelSpor.J2K.lblM
#krows CertificateChecks.KernelSpor.J2K.REP CertificateChecks.KernelSpor.J2K.repM
#krows CertificateChecks.KernelSpor.J2K.IM CertificateChecks.KernelSpor.J2K.imM
#krows CertificateChecks.KernelSpor.J2K.DS CertificateChecks.KernelSpor.J2K.dsM
#krows CertificateChecks.KernelSpor.J2K.DOFF CertificateChecks.KernelSpor.J2K.doffM
#krows CertificateChecks.KernelSpor.J2K.DLEN CertificateChecks.KernelSpor.J2K.dlenM

#ktbfs CertificateChecks.KernelSpor.J2K.CT0 315 0 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv0M
#ktbfs CertificateChecks.KernelSpor.J2K.CT1 315 4 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv1M
#ktbfs CertificateChecks.KernelSpor.J2K.CT2 315 3 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv2M

#ktbfs CertificateChecks.KernelSpor.J2K.SB0 315 0 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv1M
#ktbfs CertificateChecks.KernelSpor.J2K.SB1 315 1 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv1M
#ktbfs CertificateChecks.KernelSpor.J2K.SB2 315 2 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv1M
#ktbfs CertificateChecks.KernelSpor.J2K.SB3 315 3 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv1M
#ktbfs CertificateChecks.KernelSpor.J2K.SB4 315 4 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv1M
#ktbfs CertificateChecks.KernelSpor.J2K.SB5 315 10 CertificateChecks.KernelSpor.J2K.lettersM
  CertificateChecks.KernelSpor.J2K.lv1M

end
