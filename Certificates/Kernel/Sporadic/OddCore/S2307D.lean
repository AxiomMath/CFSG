module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.IntWordsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzOddCore.SylowCheckInputs
meta import CFSG.Sporadic.SuzOddCore.SylowCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2307

open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native

meta def gM : Array (Array Nat) := invSylowArrs
meta def giM : Array (Array Nat) := sylowInvs
meta def idM : Array Nat := idTab 1782

meta def enM : Enum := sylowEnum
meta def eM : Array (Array Nat) := enM.tabs

meta def baseM : List Nat := [0, 1]

meta def keyM : Array Nat := eM.map fun t => baseM.foldr (fun p acc => t[p]! + 1782 * acc) 0

meta def zeroM : Array Nat := Array.replicate 16384 0

meta partial def treeWordM (i : Nat) : List Int :=
  if i == 0 then [] else ((enM.lab[i]! + 1 : Nat) : Int) :: treeWordM enM.par[i]!

meta def orbitM (hs : Array (Array Nat)) (b : Nat) : Array Nat := Id.run do
  let mut seen : Array Bool := (Array.replicate 1782 false).set! b true
  let mut pts : Array Nat := #[b]
  let steps := hs ++ hs.map (invTab 1782)
  for h in [0:1782] do
    if h < pts.size then
      for s in steps do
        let y := s[pts[h]!]!
        if !seen[y]! then
          seen := seen.set! y true
          pts := pts.push y
  return pts

meta def extraM : Array Nat := Id.run do
  let mut extra : Array Nat := #[]
  for i in [0:baseM.length] do
    let pre := baseM.take i
    let b := baseM[i]!
    let fix := fun (t : Array Nat) => pre.all fun p => t[p]! == p
    let stab := (List.range eM.size).filter fun k => fix eM[k]!
    let full := (stab.map fun k => eM[k]![b]!).eraseDups.length
    let mut orb := orbitM ((gM ++ extra.map (eM[·]!)).filter fix) b
    for k in stab do
      if orb.size < full && !orb.contains eM[k]![b]! then
        extra := extra.push k
        orb := orbitM ((gM ++ extra.map (eM[·]!)).filter fix) b
  return extra

meta def sS : Array (Array Nat) := gM ++ extraM.map (eM[·]!)
meta def sBA : Array Nat := baseM.toArray

meta def sDM : Array (List Int) := extraM.map treeWordM

meta def csM : Array (Array Nat × Array Nat × Array Nat) :=
  let idx := indexOf eM
  (fusionEnums.map fun F => (F.tabs.map fun t => idx.getD t 16384, F.par, F.lab)).push
    (#[0], #[0], #[0])

meta def offM : Array Nat := Id.run do
  let mut o : Array Nat := #[0]
  for c in csM do
    o := o.push (o.back! + c.1.size)
  return o

meta def flM : Array Nat := (csM.map (·.1)).flatten
meta def fpM : Array Nat := (csM.map (·.2.1)).flatten
meta def fgM : Array Nat := (csM.map (·.2.2)).flatten

meta def fqM : Array Nat := Id.run do
  let idx := indexOf eM
  let mut out : Array Nat := #[]
  for c in csM do
    let L := c.1
    for x in L do
      for g in [0:11] do
        let m := idx.getD (conjTab 1782 gM[g]! giM[g]! eM[x]!) 16384
        out := out.push (L.idxOf m)
  return out

meta def mkM : Array Nat := Id.run do
  let mut a : Array Nat := Array.replicate 16384 22
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

end CertificateChecks.KernelSpor.S2307

#kc_intwords CertificateChecks.KernelSpor.SSD CertificateChecks.KernelSpor.S2307.sDM
#kpenum CertificateChecks.KernelSpor.SSE 1782 11 false CertificateChecks.KernelSpor.S2307.gM
  CertificateChecks.KernelSpor.S2307.giM CertificateChecks.KernelSpor.S2307.idM 16384
#kmisc_sortpair CertificateChecks.KernelSpor.SSK CertificateChecks.KernelSpor.S2307.keyM
  CertificateChecks.KernelSpor.S2307.zeroM 1 16384
#ks_rawchain CertificateChecks.KernelSpor.SSC 1782 11 64 CertificateChecks.KernelSpor.S2307.sS
  CertificateChecks.KernelSpor.S2307.sBA 11 CertificateChecks.KernelSpor.SSD
#krows CertificateChecks.KernelSpor.SSF.L CertificateChecks.KernelSpor.S2307.flM
#krows CertificateChecks.KernelSpor.SSF.P CertificateChecks.KernelSpor.S2307.fpM
#krows CertificateChecks.KernelSpor.SSF.G CertificateChecks.KernelSpor.S2307.fgM
#krows CertificateChecks.KernelSpor.SSF.Q CertificateChecks.KernelSpor.S2307.fqM
#krows CertificateChecks.KernelSpor.SSF.O CertificateChecks.KernelSpor.S2307.offM
#krows CertificateChecks.KernelSpor.SSF.MK CertificateChecks.KernelSpor.S2307.mkM
#krows CertificateChecks.KernelSpor.SSF.PX CertificateChecks.KernelSpor.S2307.pxM

end
