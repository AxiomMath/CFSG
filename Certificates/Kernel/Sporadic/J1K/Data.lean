module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Data.CFSGNative.J1.Certificate
public meta import Certificates.Data.CFSGNative.J1.Certificate

public section

namespace CertificateChecks.KernelSpor.J1K

open CFSG.Sporadic.J1.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

meta def orbM : Orb := orbitData ()

meta def codeM (v : List Nat) : Nat := (v.zipIdx.map fun (x, k) => x <<< (4 * k)).foldl (· ||| ·) 0

meta def projM (v : List Nat) : List Nat :=
  let iv := (firstNZ v) ^ 9 % 11
  v.map fun x => x * iv % 11

meta def ptM : Array Nat := orbM.pts.map codeM

meta def alM : Array Nat := orbM.alpha.map (·.toNat)
meta def beM : Array Nat := orbM.beta.map (·.toNat)
meta def paM : Array Nat := orbM.par
meta def laM : Array Nat := orbM.lab

meta def invM (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 1540 0
  for i in [0:1540] do
    r := r.set! t[i]! i
  return r

meta def aiM : Array Nat := invM alM
meta def biM : Array Nat := invM beM

meta def soM : Array Nat := ((List.range 1540).toArray.qsort fun i j => ptM[i]! < ptM[j]!)

meta def spM : Array Nat :=
  ((List.range 1540).toArray.qsort fun i j => codeM (projM orbM.pts[i]!) < codeM (projM orbM.pts[j]!))

meta def lettersM : Array Table := chainLetters orbM

meta def ltM : Array Nat := (lettersM.map fun t => t.map (·.toNat)).flatten

meta def lv0M : Array Nat := levelLetters lettersM chainBase 0
meta def lv1M : Array Nat := levelLetters lettersM chainBase 1

meta def t0M : Tree := (chainTrees 1540 lettersM chainBase)[0]!

meta def primM : PrimData := primData 1540 lettersM lv1M t0M

meta def lblM : Array Nat := primM.lab
meta def repM : Array Nat := primM.reps
meta def imM : Array Nat := primM.imgs.flatten

meta def dsM : Array Nat := (primM.ders.map fun l => (l.map fun s => s.1 * 65536 + s.2).toArray).flatten

meta def doffM : Array Nat :=
  ((List.range primM.ders.size).map fun i =>
    ((primM.ders.toList.take i).map List.length).sum).toArray

meta def dlenM : Array Nat := primM.ders.map List.length

end CertificateChecks.KernelSpor.J1K

#krows CertificateChecks.KernelSpor.J1K.PT CertificateChecks.KernelSpor.J1K.ptM
#krows CertificateChecks.KernelSpor.J1K.AL CertificateChecks.KernelSpor.J1K.alM
#krows CertificateChecks.KernelSpor.J1K.BE CertificateChecks.KernelSpor.J1K.beM
#krows CertificateChecks.KernelSpor.J1K.PA CertificateChecks.KernelSpor.J1K.paM
#krows CertificateChecks.KernelSpor.J1K.LA CertificateChecks.KernelSpor.J1K.laM
#krows CertificateChecks.KernelSpor.J1K.AI CertificateChecks.KernelSpor.J1K.aiM
#krows CertificateChecks.KernelSpor.J1K.BI CertificateChecks.KernelSpor.J1K.biM
#krows CertificateChecks.KernelSpor.J1K.SO CertificateChecks.KernelSpor.J1K.soM
#krows CertificateChecks.KernelSpor.J1K.SP CertificateChecks.KernelSpor.J1K.spM
#krows CertificateChecks.KernelSpor.J1K.LT CertificateChecks.KernelSpor.J1K.ltM
#krows CertificateChecks.KernelSpor.J1K.LBL CertificateChecks.KernelSpor.J1K.lblM
#krows CertificateChecks.KernelSpor.J1K.REP CertificateChecks.KernelSpor.J1K.repM
#krows CertificateChecks.KernelSpor.J1K.IM CertificateChecks.KernelSpor.J1K.imM
#krows CertificateChecks.KernelSpor.J1K.DS CertificateChecks.KernelSpor.J1K.dsM
#krows CertificateChecks.KernelSpor.J1K.DOFF CertificateChecks.KernelSpor.J1K.doffM
#krows CertificateChecks.KernelSpor.J1K.DLEN CertificateChecks.KernelSpor.J1K.dlenM

#ktbfs CertificateChecks.KernelSpor.J1K.CT0 1540 0 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv0M
#ktbfs CertificateChecks.KernelSpor.J1K.CT1 1540 1 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M

#ktbfs CertificateChecks.KernelSpor.J1K.SB0 1540 0 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB1 1540 1 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB2 1540 2 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB3 1540 3 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB4 1540 4 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB5 1540 6 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB6 1540 10 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB7 1540 12 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB8 1540 22 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB9 1540 23 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB10 1540 25 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB11 1540 34 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB12 1540 35 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB13 1540 37 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB14 1540 46 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB15 1540 47 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB16 1540 60 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB17 1540 67 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB18 1540 213 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB19 1540 224 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M
#ktbfs CertificateChecks.KernelSpor.J1K.SB20 1540 275 CertificateChecks.KernelSpor.J1K.lettersM
  CertificateChecks.KernelSpor.J1K.lv1M

end
