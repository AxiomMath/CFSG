module

public import Certificates.Data.HuppertU38Q.Data
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Misc.Perm.CharsLits
public import Certificates.Kernel.B3S3.GenL
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Data.HuppertU38Q.Check
public import Certificates.Data.HuppertU38.Data

public section

namespace CertificateChecks.KernelU38Q

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Certificates.Native U38Sylow

meta def xiM : List Nat := inX (qCert ()).pts (rawLevels 513 strong3 base3)

meta def wM (r : Array Nat) : List Nat :=
  let pts := (qCert ()).pts
  xiM.map fun i =>
    let x := compA 513 r pts[i]!
    ((List.range pts.size).find? fun j => eqA 513 x pts[j]!).getD 0

meta def waM : List Nat := wM qGens[0]!

meta def wbM : List Nat := wM qGens[1]!

meta def caM : List Nat := waM.filter fun j => cubeOne (qCert ()).pts[j]!

meta def cbM : List Nat := wbM.filter fun j => cubeOne (qCert ()).pts[j]!

end CertificateChecks.KernelU38Q

end

set_option maxRecDepth 400000

#ks_chars_lits CertificateChecks.KernelU38Q.QH U38Sylow.qHex
#kmisc_hexflat CertificateChecks.KernelU38Q.QH U38Sylow.qHex 3 513 10 3
#kb3_enum_l CertificateChecks.KernelU38Q.QE U38Sylow.qGens
  CFSG.RankThree.PartTwo.Sec4.Item434U38.base1 513 10
#knatlist CertificateChecks.KernelU38Q.XI CertificateChecks.KernelU38Q.xiM
#knatlist CertificateChecks.KernelU38Q.WA CertificateChecks.KernelU38Q.waM
#knatlist CertificateChecks.KernelU38Q.WB CertificateChecks.KernelU38Q.wbM
#knatlist CertificateChecks.KernelU38Q.CA CertificateChecks.KernelU38Q.caM
#knatlist CertificateChecks.KernelU38Q.CB CertificateChecks.KernelU38Q.cbM
