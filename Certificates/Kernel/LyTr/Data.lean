module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Sporadic.Recognition.LyonsAmalgamTauInputs
meta import CFSG.Sporadic.Recognition.LyonsAmalgamTauInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLyTr.GH CFSG.Sporadic.Recognition.LyonsSims.Ly243.genHex
#kmisc_hexflat CertificateChecks.KernelLyTr.GH CFSG.Sporadic.Recognition.LyonsSims.Ly243.genHex
  2 243 8 5
#ks_chars CertificateChecks.KernelLyTr.LH CFSG.Sporadic.Recognition.LyonsSims.Ly243.lineHex
#kmisc_hexflat CertificateChecks.KernelLyTr.LH CFSG.Sporadic.Recognition.LyonsSims.Ly243.lineHex
  2 243 8 3
#ks_chars CertificateChecks.KernelLyTr.UH CFSG.Sporadic.Recognition.LyonsSims.Ly1080.uHex
#kmisc_hexflat CertificateChecks.KernelLyTr.UH CFSG.Sporadic.Recognition.LyonsSims.Ly1080.uHex
  3 1080 11 4

namespace CertificateChecks.KernelLyTr

open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Recognition.LyonsSims

meta def invM (n : Nat) (t : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand n t

meta def id243M : Array Nat := idTab 243
meta def ids243M : Array (Array Nat) := Array.replicate 5 id243M
meta def genIM : Array (Array Nat) := Ly243.genTabs.map fun t => invM 243 (natArr t)
meta def lineIM : Array (Array Nat) := Ly243.lineTabs.map fun t => invM 243 (natArr t)
meta def g243M : Array (Array Nat) := Ly243.txyTabs.map natArr
meta def gi243M : Array (Array Nat) := g243M.map (invM 243)
meta def repM : Array (Array Nat) := Ly243.repTabs.map natArr
meta def repIM : Array (Array Nat) := repM.map (invM 243)
meta def rec243M : Array (Array Nat) :=
  (bfs (fun j t => conjTab 243 id243M g243M[j]! t) 5 id243M 5000).tabs
meta def cl243M : Array (Array Nat) :=
  (rec243M.map fun x => (g243M ++ gi243M).map fun g => comp 243 x g).flatten

meta def genBothM : Array (Array Nat) :=
  (Ly243.genTabs.map natArr) ++ genIM

meta def cjM : Array Nat := Id.run do
  let idx := indexOf rec243M
  let mut out : Array Nat := #[]
  for i in [0:6] do
    for m in [0:10] do
      let x := comp 243 (comp 243 repM[i]! genBothM[m]!) id243M
      let mut jj := 6
      for j in [0:6] do
        if jj == 6 && (idx.getD (comp 243 x repIM[j]!) rec243M.size) < rec243M.size then
          jj := j
      out := out.push jj
  return out

meta def cpQM : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := #[]
  for i in [0:6] do
    for m in [0:10] do
      let j := cjM[10 * i + m]!
      out := out.push (comp 243 (comp 243 repM[i]! genBothM[m]!) repIM[j % 6]!)
  return out

meta def cjRowM : Array (Array Nat) := #[cjM]

meta def id1080M : Array Nat := idTab 1080
meta def ids1080M : Array (Array Nat) := Array.replicate 5 id1080M
meta def uIM : Array (Array Nat) := Ly1080.uTabs.map fun t => invM 1080 (natArr t)
meta def g1080M : Array (Array Nat) := Ly1080.txyTabs.map natArr

end CertificateChecks.KernelLyTr

#kmulh CertificateChecks.KernelLyTr.R2 243 8 CertificateChecks.KernelLyTr.ids243M
  CertificateChecks.KernelLyTr.g243M CertificateChecks.KernelLyTr.id243M 5000
#kmisc_packarrs CertificateChecks.KernelLyTr.R2I CertificateChecks.KernelLyTr.gi243M 8
#kmisc_packarrs CertificateChecks.KernelLyTr.GHI CertificateChecks.KernelLyTr.genIM 8
#kmisc_packarrs CertificateChecks.KernelLyTr.LHI CertificateChecks.KernelLyTr.lineIM 8
#kmisc_packarrs CertificateChecks.KernelLyTr.RP CertificateChecks.KernelLyTr.repM 8
#kmisc_packarrs CertificateChecks.KernelLyTr.RPI CertificateChecks.KernelLyTr.repIM 8
#kfind CertificateChecks.KernelLyTr.R2Cl CertificateChecks.KernelLyTr.rec243M
  CertificateChecks.KernelLyTr.cl243M
#kfind CertificateChecks.KernelLyTr.CP CertificateChecks.KernelLyTr.rec243M
  CertificateChecks.KernelLyTr.cpQM
#kmisc_packarrs CertificateChecks.KernelLyTr.CJ CertificateChecks.KernelLyTr.cjRowM 3
#kmulh CertificateChecks.KernelLyTr.R1 1080 11 CertificateChecks.KernelLyTr.ids1080M
  CertificateChecks.KernelLyTr.g1080M CertificateChecks.KernelLyTr.id1080M 5000
#kmisc_packarrs CertificateChecks.KernelLyTr.UHI CertificateChecks.KernelLyTr.uIM 11
