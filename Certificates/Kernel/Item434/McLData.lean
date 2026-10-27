module

public import Certificates.Data.Item434SporMcL9
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.Item434SporMcL9
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelItem434

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.Monster.B.Co2.Native

meta def dpArrs : Array (Array Nat) := (Array.range 81).map mclDProd

meta def p9Arrs : Array (Array Nat) := (Array.range 81).map mcl9Prod

meta def dIdx (x : Array Nat) : Nat := (dpArrs.findIdx? fun d => eqA 275 x d).getD 81

meta def lineW (j : Nat) : Nat :=
  let l := mcl3Lines[j]!
  let u := dIdx l
  if u < 81 then u else
    let pts := mcl3QCert.pts
    let z := mclArr 0
    let cands := (List.range pts.size).filterMap fun k =>
      let q := pts[k]!
      if eqA 275 (conjN 275 q z) z then
        match (List.range 24).find? (fun i => eqA 275 (conjN 275 q l) (mclArr (4 + i))) with
        | some i => if mclSift q then some (81 + 24 * k + i) else none
        | none => none
      else none
    cands.headD 0

meta def lineWs : List Nat := (List.range 148).map lineW

meta def conjUs : List Nat :=
  (List.range 24).map fun i => dIdx (conjN 275 (mclArr (28 + i)) (mclArr (4 + i)))

meta def conjZs : List Nat :=
  (List.range 24).map fun i => dIdx (conjN 275 (mclArr (28 + i)) (mclArr 0))

end CertificateChecks.KernelItem434

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelItem434.MH CFSG.RankThree.PartTwo.Sec4.Item434SporGen.mclHex
#kmisc_hexflat CertificateChecks.KernelItem434.MH
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen.mclHex 3 275 9 52
#ks_chars CertificateChecks.KernelItem434.M9 CFSG.RankThree.PartTwo.Sec4.Item434SporGen.mcl9Hex
#kmisc_hexflat CertificateChecks.KernelItem434.M9
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen.mcl9Hex 3 275 9 3
#ks_chars CertificateChecks.KernelItem434.K3 CFSG.RankThree.PartTwo.KFacts.K426.mcl3Hex
#kmisc_hexflat CertificateChecks.KernelItem434.K3 CFSG.RankThree.PartTwo.KFacts.K426.mcl3Hex
  3 275 9 152
#kmisc_packarrs CertificateChecks.KernelItem434.DP CertificateChecks.KernelItem434.dpArrs 9
#kmisc_packarrs CertificateChecks.KernelItem434.P9 CertificateChecks.KernelItem434.p9Arrs 9
#kss_natlist CertificateChecks.KernelItem434.LW CertificateChecks.KernelItem434.lineWs
#kss_natlist CertificateChecks.KernelItem434.CU CertificateChecks.KernelItem434.conjUs
#kss_natlist CertificateChecks.KernelItem434.CZ CertificateChecks.KernelItem434.conjZs
