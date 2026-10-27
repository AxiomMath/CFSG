module

public import Certificates.Kernel.HeLoc.FiveData
public meta import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
public meta import CFSG.Monster.B.Mathieu.SylowCore

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne

meta def arrsM : Array (Array Nat) := Array.ofFn fun j : Fin 13 => heFiveArr j.val

meta def invsM : Array (Array Nat) := arrsM.map (invCand 8330)

meta def inPM (g : Array Nat) : Bool :=
  siftA 8330 CFSG.Sporadic.HeldB.heLevels CFSG.Sporadic.HeldB.heBase.toArray 0 g

meta def flagsM : List Nat := arrsM.toList.map fun g => if inPM g then 0 else 1

meta def nfsM : List Nat := arrsM.toList.map fun g =>
  if inPM g then Five.nfOf g else Five.nfOf (compA 8330 g CFSG.Sporadic.HeldB.heUArr)

meta def qwM : List Nat :=
  let pw : Array (Nat × Array Nat) := Id.run do
    let mut r := #[]
    for j in [0:6] do
      for e in [1:5] do
        r := r.push (8 * j + e, CFSG.Monster.B.Mathieu.powArr 8330 heFiveLines[j]! e)
    return r
  heFiveQCert.pts.toList.map fun t =>
    ((pw.toList.find? fun c => eqA 8330 t c.2).map (·.1)).getD 0

meta def lqM : List Nat := (List.range 6).map fun j =>
  ((List.range heFiveQCert.pts.size).find? fun k =>
    eqA 8330 heFiveQCert.pts[k]! heFiveLines[j]!).getD 0

end CertificateChecks.KernelHeLoc.FiveL

#kss_perms CertificateChecks.KernelHeLoc.FiveL.AI5 14 CertificateChecks.KernelHeLoc.FiveL.invsM
#knatlist CertificateChecks.KernelHeLoc.FiveL.FL5 CertificateChecks.KernelHeLoc.FiveL.flagsM
#knatlist CertificateChecks.KernelHeLoc.FiveL.NF5 CertificateChecks.KernelHeLoc.FiveL.nfsM
#kh_tree CertificateChecks.KernelHeLoc.FiveL.Q CFSG.RankThree.PartOne.heFiveQCert 8330
  CFSG.RankThree.PartOne.heFiveKeys
#knatlist CertificateChecks.KernelHeLoc.FiveL.QW CertificateChecks.KernelHeLoc.FiveL.qwM
#knatlist CertificateChecks.KernelHeLoc.FiveL.LQ CertificateChecks.KernelHeLoc.FiveL.lqM

end
