module

public import Certificates.Kernel.U38R.Base
public import Certificates.Kernel.Sporadic.OrbRecGen
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Kernel.U38R.Base

public section

namespace CertificateChecks.KernelU38R

open CFSG.RankThree.PartTwo.Sec18.Item185Proof.U38Elim CFSG.RankThree.PartTwo.Sec4.Item434U38
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer

meta def elimE : Array (Array Nat) := (rCert ()).pts

meta def elimT : Array (Array Nat) := mulTab elimE

meta def elimX : Array Bool := inXArr (rawLevels 513 strong3 base3) elimE

meta def s3M : List Nat :=
  (List.range 729).filter fun i => elimX[i]! && i != 0 && cubeI elimT i

meta def cmOf (i : Nat) : Nat :=
  (List.range 729).foldl (fun acc x => if commI elimT x i then acc ||| (1 <<< x) else acc) 0

meta def cmM : Array Nat := (Array.range 729).map fun i => if s3M.contains i then cmOf i else 0

meta def guardM (i1 i2 : Nat) : Bool :=
  commI elimT i1 i2 && i2 != i1 && i2 != mulI elimT i1 i1

meta def keyM (i1 i2 : Nat) : List Nat × Nat :=
  ((belems elimT i1 i2).mergeSort, cmM[i1]! &&& cmM[i2]!)

meta def keysM : Array (List Nat × Nat) :=
  s3M.foldl (fun ks i1 => s3M.foldl (fun ks i2 =>
    if guardM i1 i2 then (let k := keyM i1 i2; if ks.contains k then ks else ks.push k) else ks)
    ks) #[]

meta def kOf (i1 i2 : Nat) : Nat := (keysM.findIdx? (· == keyM i1 i2)).getD 15

meta def pkM : Array Nat := (Array.range 729).map fun i1 =>
  (List.range 729).foldl (fun acc i2 =>
    acc ||| ((if s3M.contains i1 && s3M.contains i2 && guardM i1 i2 then kOf i1 i2 else 15) <<<
      (4 * i2))) 0

meta def cnM : Array Nat := (Array.range 16).map fun k => (keysM[k]?.map (·.2)).getD 0

meta def bkM : Array Nat := (Array.range 16).map fun k =>
  ((keysM[k]?.map (·.1)).getD []).zipIdx.foldl (fun acc (b, t) => acc ||| (b <<< (10 * t))) 0

meta def twOf (k : Nat) : Nat :=
  match keysM[k]? with
  | none => 0
  | some (bl, cm) =>
    let cen := (List.range 729).filter fun x => (cm >>> x) &&& 1 == 1
    (List.range 729).foldl (fun acc j =>
      if (cm >>> j) &&& 1 == 1 && !elimX[j]! && cubeI elimT j then
        let t := (bl.findIdx? fun b => refD2 elimT cen [b] j).getD 15
        acc ||| (t <<< (4 * j))
      else acc) 0

meta def twM : Array Nat := (Array.range 16).map twOf

end CertificateChecks.KernelU38R

end

set_option maxRecDepth 400000

#knatlist CertificateChecks.KernelU38R.S3L CertificateChecks.KernelU38R.s3M
#kc_nattree CertificateChecks.KernelU38R.CM CertificateChecks.KernelU38R.cmM
#kc_nattree CertificateChecks.KernelU38R.PK CertificateChecks.KernelU38R.pkM
#kc_nattree CertificateChecks.KernelU38R.CN CertificateChecks.KernelU38R.cnM
#kc_nattree CertificateChecks.KernelU38R.BK CertificateChecks.KernelU38R.bkM
#kc_nattree CertificateChecks.KernelU38R.TW CertificateChecks.KernelU38R.twM
