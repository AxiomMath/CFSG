module

public import Certificates.Data.KD4BU38.Data
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Misc.Perm.CharsLits
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Data.KD4BU38.Data
public meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelU38

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Certificates.Native
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.PGU38Classes

@[expose] def dX : List (List Int) := words3.toList.drop 7

meta def classWitM : List Nat :=
  let L := (pgu38SylowEnum ()).pts
  (List.range L.size).map fun i =>
    let x := L[i]!
    if eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 x 3) (idA 513) && !eqA 513 x (idA 513) then
      ((List.range L.size).findSome? fun h =>
        let c := conjA 513 L[h]! x
        ((List.range 10).find? fun j => eqA 513 c pgu38ClassReps[j]!).map fun j => 16 * h + j).getD 0
    else 0

meta def repWitM : List Nat :=
  (List.range 10).map fun j =>
    let c := conjA 513 pgu38RepConj[j]! pgu38ClassReps[j]!
    ((List.range 5).find? fun r => eqA 513 c pgu38ClassReps[pgu38RepIdx[r]!]!).getD 0

end CertificateChecks.KernelU38

end

set_option maxRecDepth 400000

#ks_chars_lits CertificateChecks.KernelU38.UF CFSG.LocalAnalysis.GLTheoremA.KD264Lie.PGU38Classes.pgu38Hex
#kmisc_hexflat CertificateChecks.KernelU38.UF
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.PGU38Classes.pgu38Hex 3 513 10 28
#ks_chars_lits CertificateChecks.KernelU38.UH CFSG.RankThree.PartTwo.Sec4.Item434U38.permHex
#kmisc_hexflat CertificateChecks.KernelU38.UH CFSG.RankThree.PartTwo.Sec4.Item434U38.permHex 3 513 10 25
#kb3_enum CertificateChecks.KernelU38.UQ
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.PGU38Classes.pgu38SylowGens
  CFSG.RankThree.PartTwo.Sec4.Item434U38.base1 513 10
#ks_rawchain CertificateChecks.KernelU38.UX 513 10 0 CFSG.RankThree.PartTwo.Sec4.Item434U38.strong3
  CFSG.RankThree.PartTwo.Sec4.Item434U38.base3 7 CertificateChecks.KernelU38.dX
#knatlist CertificateChecks.KernelU38.CW CertificateChecks.KernelU38.classWitM
#knatlist CertificateChecks.KernelU38.RW CertificateChecks.KernelU38.repWitM
