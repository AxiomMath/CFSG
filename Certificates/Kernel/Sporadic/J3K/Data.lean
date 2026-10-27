module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.J3.Data

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.J3SeedA CFSG.Sporadic.J3.Native.seedA
#ks_chars CertificateChecks.KernelSpor.J3SeedB CFSG.Sporadic.J3.Native.seedB

namespace CertificateChecks.KernelSpor.J3K

open CFSG.Sporadic.J3.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

meta def DM : Data := j3Data ()
meta def ptsM : Array Nat := DM.pts
meta def taM : Array Nat := DM.tA.map (·.toNat)
meta def tbM : Array Nat := DM.tB.map (·.toNat)

meta def invM (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 20520 0
  for i in [0:20520] do
    r := r.set! t[i]! i
  return r

meta def aiM : Array Nat := invM taM
meta def biM : Array Nat := invM tbM

meta def bfsM : Array Nat × Array Nat := Id.run do
  let root := (ptsM.toList.idxOf DM.v0)
  let mut seen := (Array.replicate 20520 false).set! root true
  let mut ord : Array Nat := #[root]
  let mut par : Array Nat := #[0]
  for h in [0:20520] do
    if h < ord.size then
      let p := ord[h]!
      for q in [taM[p]!, tbM[p]!] do
        if !seen[q]! then
          seen := seen.set! q true
          ord := ord.push q
          par := par.push h
  return (ord, par)

meta def boM : Array Nat := bfsM.1
meta def bqM : Array Nat := bfsM.2
meta def boiM : Array Nat := invM boM

meta def caM : List Nat := (transposeRows 80 DM.rowsA).toList
meta def cbM : List Nat := (transposeRows 80 DM.rowsB).toList
meta def raM : List Nat := DM.rowsA.toList
meta def rbM : List Nat := DM.rowsB.toList

meta def lettersM : Array Table := DM.letters
meta def ltM : Array Nat := (lettersM.map fun t => t.map (·.toNat)).flatten
meta def lv0M : Array Nat := levelLetters lettersM DM.base 0
meta def lv1M : Array Nat := DM.lv
meta def lblM : Array Nat := DM.labs

meta def dsM : Array Nat := (DM.derivs.map fun l => (l.map fun s => s.1 * 65536 + s.2).toArray).flatten

meta def doffM : Array Nat :=
  ((List.range DM.derivs.size).map fun i => ((DM.derivs.toList.take i).map List.length).sum).toArray

meta def dlenM : Array Nat := DM.derivs.map List.length

end CertificateChecks.KernelSpor.J3K

#knatlist CertificateChecks.KernelSpor.J3K.CAL CertificateChecks.KernelSpor.J3K.caM
#knatlist CertificateChecks.KernelSpor.J3K.CBL CertificateChecks.KernelSpor.J3K.cbM
#knatlist CertificateChecks.KernelSpor.J3K.RAL CertificateChecks.KernelSpor.J3K.raM
#knatlist CertificateChecks.KernelSpor.J3K.RBL CertificateChecks.KernelSpor.J3K.rbM
#krowsw CertificateChecks.KernelSpor.J3K.PT 80 CertificateChecks.KernelSpor.J3K.ptsM
#krows CertificateChecks.KernelSpor.J3K.TA CertificateChecks.KernelSpor.J3K.taM
#krows CertificateChecks.KernelSpor.J3K.TB CertificateChecks.KernelSpor.J3K.tbM
#krows CertificateChecks.KernelSpor.J3K.AI CertificateChecks.KernelSpor.J3K.aiM
#krows CertificateChecks.KernelSpor.J3K.BI CertificateChecks.KernelSpor.J3K.biM
#krows CertificateChecks.KernelSpor.J3K.BO CertificateChecks.KernelSpor.J3K.boM
#krows CertificateChecks.KernelSpor.J3K.BOI CertificateChecks.KernelSpor.J3K.boiM
#krows CertificateChecks.KernelSpor.J3K.BQ CertificateChecks.KernelSpor.J3K.bqM
#krows CertificateChecks.KernelSpor.J3K.LT CertificateChecks.KernelSpor.J3K.ltM
#krows CertificateChecks.KernelSpor.J3K.LBL CertificateChecks.KernelSpor.J3K.lblM
#krows CertificateChecks.KernelSpor.J3K.DS CertificateChecks.KernelSpor.J3K.dsM
#krows CertificateChecks.KernelSpor.J3K.DOFF CertificateChecks.KernelSpor.J3K.doffM
#krows CertificateChecks.KernelSpor.J3K.DLEN CertificateChecks.KernelSpor.J3K.dlenM

#ktbfs CertificateChecks.KernelSpor.J3K.CT0 20520 0 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv0M
#ktbfs CertificateChecks.KernelSpor.J3K.CT1 20520 1 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M

#ktbfs CertificateChecks.KernelSpor.J3K.SB0 20520 0 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB1 20520 1 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB2 20520 2 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB3 20520 3 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB4 20520 4 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB5 20520 5 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB6 20520 6 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB7 20520 7 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB8 20520 8 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB9 20520 9 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB10 20520 11 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB11 20520 17 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB12 20520 18 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB13 20520 19 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB14 20520 27 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB15 20520 28 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB16 20520 33 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB17 20520 34 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB18 20520 80 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB19 20520 95 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB20 20520 132 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M
#ktbfs CertificateChecks.KernelSpor.J3K.SB21 20520 135 CertificateChecks.KernelSpor.J3K.lettersM
  CertificateChecks.KernelSpor.J3K.lv1M

end
