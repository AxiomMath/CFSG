module

public import Certificates.Kernel.HeLoc.TreeCmd
public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Certificates.Kernel.Spor.PackWord
public import Certificates.Data.K426J3
public meta import Certificates.Data.K426J3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK426J3

open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.KFacts.K426

meta def invsM : Array (Array Nat) := (Array.range 40).map fun k => invCand 6156 (j3tArr k)

meta def idxOf (c : CFSG.Monster.B.Fischer.ArrCert) (t : Array Nat) : Nat :=
  ((List.range c.pts.size).find? fun k => eqA 6156 c.pts[k]! t).getD c.pts.size

meta def dwM : List Nat :=
  ((List.range 8).map fun m => idxOf j3tDCert (conjA 6156 j3tCAGens[m / 2]! j3tDGens[m % 2]!)) ++
    (List.range 16).map fun m =>
      idxOf j3tDCert (commutatorA 6156 j3tCAGens[m / 4]! j3tCAGens[m % 4]!)

@[expose] def WS : List (List Int) :=
  [[2, -5], [3, 2, -3, 2, 4, -2, -5, 1, 3, 5, 1], [1, -5, 3, 1, -2, 1, 2, 1, 5, 3, 5, 3, 1, 5],
    [1, -5, 1, 2, 1, -2, 1, 3, 5, -3, 1, 3, 4, 5], [-2, 4, -2, 3, 3, 2, 1, -5, 1, -5, 3, 1, 4, -5],
    [5], [2], [2, -5], [2, 5], [3, 2, -3, 5, 3, 3, 2, 3, 3, 1, -3, 1, 3, 4],
    [3, 2, -3, 5, 3, 3, 2, 3, 3, 1, -3, 1, 3, 4, 5], [3, 2, -3, 5, 3, 3, 2, 3, 3, 1, -3, 1, 3, 4, -5],
    [1, -5, 3, 1, -2, 1, 2, 1, 5, 3, 5, 3, 1], [1, -5, 3, 1, -2, 1, 2, 1, 5, 3, 5, 3, 1, 5],
    [1, -5, 3, 1, -2, 1, 2, 1, 5, 3, 5, 3, 1, -5], [1, 3, 2, -3, 1, 5, 1, 2, -3, 1, -3, 4, 3, 4, 5],
    [1, 3, 2, -3, 1, 5, 1, 2, -3, 1, -3, 4, 3, 4], [1, 3, 2, -3, 1, 5, 1, 2, -3, 1, -3, 4, 3, 4, -5],
    [2], [2, -5], [3, 3, -2, -5, 1, -3, 4], [], [], [-3, -3, -2, 5, -3, 1, 5, 1, 3, 1],
    [1, 2, 4, -2, 4, -3, -3, 1, -3, 4], [1, 2, -5, 1, -3, -3, 5, -3, 4], [1, -2, -3, -3, 1, 3, 4],
    [1, -2, 1, 2, 5, -3, 5, 3, 1, 4], [4, 3, 1, -2, 1, 5, -3, -5, 1, 4], [1, -3, 2, 3, 1, 3, 3, 3, 4],
    [3, 1, 3, 2, 1, -3, 1, 3, 5, 3, 4], [4, -2, -3, -5, 1, 5, 3], [4, -2, -3, -5, 1, 5, 3], [2],
    [1, 5, 4, -2, 3, 2, 1, -5, -3, 1, -3], [-2, 4, -3, 1, -2, 1, -2, -3, 5, 1, 5, 3, 1, 4, 5],
    [-3, -2, 4, -2, 5, 1, 2, -3, -5, 1, -3, -5, 1, -5], [5, 1, -3, 4, 2, -3, 2, -3, 1, -3, 5, 3, 5],
    [4, -3, 1, -2, 1, -2, -3, 5, 1, 5, 3, 1, 4, 5], [1, -2, 4, 3, -5, 1, 2, -5, 1, 5, 3, 3, 1, 4]]

end CertificateChecks.KernelK426J3

#kh_tree CertificateChecks.KernelK426J3.TQ CFSG.RankThree.PartTwo.KFacts.K426.j3tCBCert 6156
  CFSG.RankThree.PartTwo.KFacts.K426.j3tKeys
#kh_tree CertificateChecks.KernelK426J3.TA CFSG.RankThree.PartTwo.KFacts.K426.j3tCACert 6156
  CFSG.RankThree.PartTwo.KFacts.K426.j3tKeys
#kh_tree CertificateChecks.KernelK426J3.TD CFSG.RankThree.PartTwo.KFacts.K426.j3tDCert 6156
  CFSG.RankThree.PartTwo.KFacts.K426.j3tKeys
#kss_perms CertificateChecks.KernelK426J3.FI 13 CertificateChecks.KernelK426J3.invsM
#knatlist CertificateChecks.KernelK426J3.DW CertificateChecks.KernelK426J3.dwM

end
