module

public import Certificates.Kernel.HeLoc.TreeCmd
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Mathlib
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne

meta def arrsM : Array (Array Nat) := Array.ofFn fun j : Fin 75 => heSevenArr j.val

meta def invsM : Array (Array Nat) := arrsM.map (invCand 8330)

meta def inPM (g : Array Nat) : Bool :=
  siftA 8330 CFSG.Sporadic.HeldB.heLevels CFSG.Sporadic.HeldB.heBase.toArray 0 g

meta def nfOf (g : Array Nat) : Nat :=
  let nf := CFSG.Sporadic.Schreier.PairNative.decodeNF CFSG.Sporadic.HeldB.heLevels
    ((CFSG.Sporadic.HeldB.heBase.map fun b => g[b]!).toArray)
  (List.range nf.size).foldl (fun acc i => acc ||| (nf[i]! <<< (16 * i))) 0

meta def flagsM : List Nat := arrsM.toList.map fun g => if inPM g then 0 else 1

meta def nfsM : List Nat := arrsM.toList.map fun g =>
  if inPM g then nfOf g else nfOf (compA 8330 g CFSG.Sporadic.HeldB.heUArr)

meta def qwM : List Nat :=
  let pw : Array (Nat × Array Nat) := Id.run do
    let mut r := #[]
    for j in [0:57] do
      for e in [1:7] do
        r := r.push (8 * j + e, CFSG.Monster.B.Mathieu.powArr 8330 heSevenLines[j]! e)
    return r
  heSevenQCert.pts.toList.map fun t =>
    ((pw.toList.find? fun c => eqA 8330 t c.2).map (·.1)).getD 0

meta def lqM : List Nat := (List.range 57).map fun j =>
  ((List.range heSevenQCert.pts.size).find? fun k =>
    eqA 8330 heSevenQCert.pts[k]! heSevenLines[j]!).getD 0

end CertificateChecks.KernelHeLoc.Seven

#ks_chars CertificateChecks.KernelHeLoc.Seven.SH CFSG.RankThree.PartOne.heSevenHex
#kmisc_hexflat CertificateChecks.KernelHeLoc.Seven.SH CFSG.RankThree.PartOne.heSevenHex 4 8330 14 75
#kss_perms CertificateChecks.KernelHeLoc.Seven.SI 14 CertificateChecks.KernelHeLoc.Seven.invsM
#knatlist CertificateChecks.KernelHeLoc.Seven.FL CertificateChecks.KernelHeLoc.Seven.flagsM
#knatlist CertificateChecks.KernelHeLoc.Seven.NF CertificateChecks.KernelHeLoc.Seven.nfsM
#kh_tree CertificateChecks.KernelHeLoc.Seven.Q CFSG.RankThree.PartOne.heSevenQCert 8330
  CFSG.RankThree.PartOne.heSevenKeys
#knatlist CertificateChecks.KernelHeLoc.Seven.QW CertificateChecks.KernelHeLoc.Seven.qwM
#knatlist CertificateChecks.KernelHeLoc.Seven.LQ CertificateChecks.KernelHeLoc.Seven.lqM

end
