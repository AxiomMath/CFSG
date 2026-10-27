module

public import Certificates.Kernel.U38R.Base
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Misc.Perm.CharsLits
public import Certificates.Kernel.B3S3.GenL
public import Certificates.Kernel.Sporadic.OrbRecGen
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Kernel.U38R.Base

public section

namespace CertificateChecks.KernelU38R

open CFSG.RankThree.PartTwo.Sec18.Item185Proof.U38Elim CFSG.RankThree.PartTwo.Sec4.Item434U38
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer

meta def keyRowsM : Array Nat :=
  let E := (rCert ()).pts
  (List.range E.size).foldl (fun (rows : Array Nat) m =>
    let a := (E[m]!)[0]!
    let b := (E[m]!)[1]!
    rows.modify b fun r => r ||| (m <<< (10 * a))) (Array.replicate 513 0)

meta def inXM : List Nat :=
  let E := (rCert ()).pts
  let lev3 := rawLevels 513 strong3 base3
  [(List.range E.size).foldl
    (fun acc i => if siftA 513 lev3 base3 0 E[i]! then acc ||| (1 <<< i) else acc) 0]

end CertificateChecks.KernelU38R

end

set_option maxRecDepth 400000

#ks_chars_lits CertificateChecks.KernelU38R.RH
  CFSG.RankThree.PartTwo.Sec18.Item185Proof.U38Elim.dataHex
#kmisc_hexflat CertificateChecks.KernelU38R.RH
  CFSG.RankThree.PartTwo.Sec18.Item185Proof.U38Elim.dataHex 3 513 10 12
#kb3_enum_l CertificateChecks.KernelU38R.UR CertificateChecks.KernelU38R.rGensA
  CertificateChecks.KernelU38R.psA 513 10
#kc_nattree CertificateChecks.KernelU38R.KR CertificateChecks.KernelU38R.keyRowsM
#knatlist CertificateChecks.KernelU38R.IXL CertificateChecks.KernelU38R.inXM
