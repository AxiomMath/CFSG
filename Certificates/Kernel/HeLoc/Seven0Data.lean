module

public import Certificates.Kernel.HeLoc.TreeCmd
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public meta import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public meta import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Mathlib
public import Mathlib

public section

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne CFSG.RankThree.Native

meta def forceOf (rels : List (Nat × Nat × Nat)) (nb : Nat) : List Nat :=
  (List.range nb).map fun i =>
    match rels.find? (fun r => r.2.1 == i && decide (r.1 < i)) with
    | some r => 8 * r.1 + r.2.2 + 1
    | none => 0

meta def idxOf (c : CFSG.Monster.B.Fischer.ArrCert) (t : Array Nat) : Nat :=
  ((List.range c.pts.size).find? fun k => eqA 8330 c.pts[k]! t).getD 0

meta def fr0M : List Nat := forceOf heSevenCase0Rels 14

meta def aw0M : List Nat := heSevenA0Gens.toList.map (idxOf heSevenC0Cert)

meta def cw0M : List Nat := (List.range 9).map fun m =>
  idxOf heSevenA0Cert (conjA 8330 heSevenC0Gens[m / 3]! heSevenA0Gens[m % 3]!)

meta def xw0M : List Nat := [idxOf heSevenA0Cert heSevenLines[0]!]

meta def zw0M : List Nat := heSevenC0Cert.pts.toList.map fun c =>
  match (List.range 3).find? (fun l => !commA 8330 c heSevenA0Gens[l]!) with
  | some l => l + 1
  | none => ((List.range 7).find? (fun e =>
      eqA 8330 c (CFSG.Monster.B.Mathieu.powArr 8330 heSevenLines[0]! e))).getD 0 + 100

end CertificateChecks.KernelHeLoc.Seven

#kh_tree CertificateChecks.KernelHeLoc.Seven.C0 CFSG.RankThree.PartOne.heSevenC0Cert 8330
  CFSG.RankThree.PartOne.heSevenKeys
#kh_tree CertificateChecks.KernelHeLoc.Seven.A0 CFSG.RankThree.PartOne.heSevenA0Cert 8330
  CFSG.RankThree.PartOne.heSevenKeys
#knatlist CertificateChecks.KernelHeLoc.Seven.FR0 CertificateChecks.KernelHeLoc.Seven.fr0M
#knatlist CertificateChecks.KernelHeLoc.Seven.AW0 CertificateChecks.KernelHeLoc.Seven.aw0M
#knatlist CertificateChecks.KernelHeLoc.Seven.CW0 CertificateChecks.KernelHeLoc.Seven.cw0M
#knatlist CertificateChecks.KernelHeLoc.Seven.XW0 CertificateChecks.KernelHeLoc.Seven.xw0M
#knatlist CertificateChecks.KernelHeLoc.Seven.ZW0 CertificateChecks.KernelHeLoc.Seven.zw0M

end
