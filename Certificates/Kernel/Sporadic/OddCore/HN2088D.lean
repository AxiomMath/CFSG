module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.HNOddCore.PCheckInputs
meta import CFSG.Sporadic.HNOddCore.PCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2088

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData
open CFSG.ONSchreier.Native

meta def pgM : Array (Array Nat) := pgenPerms
meta def pgiM : Array (Array Nat) := pinvs 800 pgenPerms
meta def idM : Array Nat := pid 800

meta def eM : Array (Array Nat) := pEnum pgenPerms parRecs

meta def baseM : List Nat := [0, 4, 3, 1, 2]

meta def keyM : Array Nat := eM.map fun t => baseM.foldr (fun p acc => t[p]! + 800 * acc) 0

meta def zeroM : Array Nat := Array.replicate 16384 0

meta def csM : Array (Array Nat × Array Nat × Array Nat) :=
  pReps.map fun r => conjOrbit (pIdx eM) eM pgenPerms (pinvs 800 pgenPerms) r

meta def offM : Array Nat := Id.run do
  let mut o : Array Nat := #[0]
  for c in csM do
    o := o.push (o.back! + c.1.size)
  return o

meta def flM : Array Nat := (csM.map (·.1)).flatten
meta def fpM : Array Nat := (csM.map (·.2.1)).flatten
meta def fgM : Array Nat := (csM.map (·.2.2)).flatten

meta def fqM : Array Nat := Id.run do
  let idx := pIdx eM
  let pgi := pinvs 800 pgenPerms
  let mut out : Array Nat := #[]
  for c in csM do
    let L := c.1
    for x in L do
      for g in [0:14] do
        let m := idx.getD (pconj pgenPerms[g]! pgi[g]! eM[x]!) 16384
        out := out.push (L.idxOf m)
  return out

meta def mkM : Array Nat := Id.run do
  let mut a : Array Nat := Array.replicate 16384 29
  for c in [0:csM.size] do
    for x in csM[c]!.1 do
      a := a.set! x c
  return a

meta def pxM : Array Nat := Id.run do
  let mut a : Array Nat := Array.replicate 16384 0
  for c in [0:csM.size] do
    let L := csM[c]!.1
    for j in [0:L.size] do
      a := a.set! L[j]! j
  return a

meta def pbS : Array (Array Nat) := strongArrs 800 pgenPerms QData.pbarWords
meta def pbBA : Array Nat := (QData.pbarBase.map Fin.val).toArray
@[expose] def pbD : List (List Int) := (QData.pbarWords.extract 14 QData.pbarWords.size).toList

end CertificateChecks.KernelSpor.HN2088

#kpenum CertificateChecks.KernelSpor.HPE 800 10 false CertificateChecks.KernelSpor.HN2088.pgM
  CertificateChecks.KernelSpor.HN2088.pgiM CertificateChecks.KernelSpor.HN2088.idM 16384
#kmisc_sortpair CertificateChecks.KernelSpor.HPSK CertificateChecks.KernelSpor.HN2088.keyM
  CertificateChecks.KernelSpor.HN2088.zeroM 1 16384
#ks_rawchain CertificateChecks.KernelSpor.HPC 800 10 64 CertificateChecks.KernelSpor.HN2088.pbS
  CertificateChecks.KernelSpor.HN2088.pbBA 14 CertificateChecks.KernelSpor.HN2088.pbD
#krows CertificateChecks.KernelSpor.HPF.L CertificateChecks.KernelSpor.HN2088.flM
#krows CertificateChecks.KernelSpor.HPF.P CertificateChecks.KernelSpor.HN2088.fpM
#krows CertificateChecks.KernelSpor.HPF.G CertificateChecks.KernelSpor.HN2088.fgM
#krows CertificateChecks.KernelSpor.HPF.Q CertificateChecks.KernelSpor.HN2088.fqM
#krows CertificateChecks.KernelSpor.HPF.O CertificateChecks.KernelSpor.HN2088.offM
#krows CertificateChecks.KernelSpor.HPF.MK CertificateChecks.KernelSpor.HN2088.mkM
#krows CertificateChecks.KernelSpor.HPF.PX CertificateChecks.KernelSpor.HN2088.pxM

end
