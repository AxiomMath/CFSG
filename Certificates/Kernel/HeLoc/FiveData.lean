module

public import Certificates.Kernel.HeLoc.TreeCmd
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
public import CFSG.Sporadic.HeldB.AutData
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
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

namespace CertificateChecks.KernelHeLoc.Five

open CFSG.Monster.B.Co2.Native

meta def invsM : Array (Array Nat) :=
  CFSG.RankThree.PartOne.heFiveC0Gens.map (invCand 8330)

meta def nfOf (g : Array Nat) : Nat :=
  let nf := CFSG.Sporadic.Schreier.PairNative.decodeNF CFSG.Sporadic.HeldB.heLevels
    ((CFSG.Sporadic.HeldB.heBase.map fun b => g[b]!).toArray)
  (List.range nf.size).foldl (fun acc i => acc ||| (nf[i]! <<< (16 * i))) 0

meta def nfsM : List Nat :=
  [nfOf CFSG.RankThree.PartOne.heFiveC0Gens[0]!, nfOf CFSG.RankThree.PartOne.heFiveC0Gens[2]!,
    nfOf (compA 8330 CFSG.RankThree.PartOne.heFiveC0Gens[1]! CFSG.Sporadic.HeldB.heUArr)]

end CertificateChecks.KernelHeLoc.Five

#ks_chars CertificateChecks.KernelHeLoc.Five.FH CFSG.RankThree.PartOne.heFiveHex
#kmisc_hexflat CertificateChecks.KernelHeLoc.Five.FH CFSG.RankThree.PartOne.heFiveHex 4 8330 14 13
#ks_chars CertificateChecks.KernelHeLoc.Five.AR CFSG.Sporadic.HeldB.heAutRHex
#kmisc_hexflat CertificateChecks.KernelHeLoc.Five.AR CFSG.Sporadic.HeldB.heAutRHex 4 8330 14 1
#kss_perms CertificateChecks.KernelHeLoc.Five.FI 14 CertificateChecks.KernelHeLoc.Five.invsM
#kh_tree CertificateChecks.KernelHeLoc.Five.C0 CFSG.RankThree.PartOne.heFiveC0Cert 8330
  CFSG.RankThree.PartOne.heFiveKeys
#knatlist CertificateChecks.KernelHeLoc.Five.NF CertificateChecks.KernelHeLoc.Five.nfsM

end
