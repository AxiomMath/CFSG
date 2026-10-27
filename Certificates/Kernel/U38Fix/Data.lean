module

public import Certificates.Data.HuppertU38Fix.Data
public import Certificates.Kernel.U38Q.Data
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Misc.Perm.CharsLits
public import Certificates.Kernel.B3S3.GenL
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Data.HuppertU38Fix.Check
public meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelU38Fix

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Certificates.Native U38Sylow U38Fix

meta def e0M : List Nat := (e0List ()).map (CFSG.KS.RawGen.pack 10)

meta def fwM : List Nat :=
  let pts := (hCert ()).pts
  let lev3 := rawLevels 513 strong3 base3
  [((List.range pts.size).find? fun i =>
    cubeComm pts[i]! && !isIdA pts[i]! && inXA lev3 pts[i]!).getD 0]

meta def cvM : List Nat :=
  let pts := (qCert ()).pts
  let hl := (idA 513 :: tHs.toList).toArray
  let E0 := (e0List ()).toArray
  CertificateChecks.KernelU38Q.xiM.map fun z =>
    let x := pts[z]!
    if !cubeOne x || isIdA x then 0 else
      ((List.range 4).findSome? fun t =>
        CertificateChecks.KernelU38Q.xiM.findSome? fun y =>
          let u := compA 513 hl[t]! pts[y]!
          let v := compA 513 u x
          ((List.range 9).find? fun e => eqA 513 v (compA 513 E0[e]! u)).map
            fun e => t + 4 * (e + 9 * y)).getD 0

end CertificateChecks.KernelU38Fix

end

set_option maxRecDepth 400000

#ks_chars_lits CertificateChecks.KernelU38Fix.FH U38Fix.fixHex
#kmisc_hexflat CertificateChecks.KernelU38Fix.FH U38Fix.fixHex 3 513 10 8
#kb3_enum_l CertificateChecks.KernelU38Fix.HE U38Fix.hGens
  CFSG.RankThree.PartTwo.Sec4.Item434U38.base1 513 10
#knatlist CertificateChecks.KernelU38Fix.E0K CertificateChecks.KernelU38Fix.e0M
#knatlist CertificateChecks.KernelU38Fix.FW CertificateChecks.KernelU38Fix.fwM
#knatlist CertificateChecks.KernelU38Fix.CV CertificateChecks.KernelU38Fix.cvM
