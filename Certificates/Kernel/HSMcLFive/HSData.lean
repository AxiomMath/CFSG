module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.B3S3.Gen
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import Certificates.Kernel.B3S3.Gen
meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Kernel.LocalComp.BfsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHSMcLFive

@[expose] def d0 : List (List Int) := CFSG.RankThree.Native.hs100Case0Words.toList.drop 3

@[expose] def d2 : List (List Int) := CFSG.RankThree.Native.hs100Case2Words.toList.drop 3

@[expose] def d23 : List (List Int) := CFSG.RankThree.Native.hs100Case23Words.toList.drop 3

open CFSG.KC.BfsGen CFSG.KS.RawGen in
meta def dGensM : Array (Array Nat) :=
  let g1 := CFSG.RankThree.Native.hs100FiveC2Gens[1]!
  let g2 := CFSG.RankThree.Native.hs100FiveC2Gens[2]!
  #[comp 100 (comp 100 g1 g2) (comp 100 (inv 100 g1) (inv 100 g2)), g2]

open CFSG.KC.BfsGen CFSG.KS.RawGen in
meta def wtM : Array (Array Nat) :=
  let as := (search 100 7 dGensM).1
  let N := as.size
  let idx : Std.HashMap Nat Nat := (Array.range N).foldl (fun m i => m.insert (pack 7 as[i]!) i) {}
  as.map fun ak => Id.run do
    let mut rs : Array Nat := Array.replicate N 0
    if ak == Array.range 100 then return rs
    let cs := as.map fun aj => comp 100 aj (comp 100 ak (inv 100 aj))
    let mut seen : Array Bool := (Array.replicate N false).set! 0 true
    let mut q : Array Nat := #[0]
    let mut h := 0
    while h < q.size do
      let p := q[h]!
      for j in [0:N] do
        let y := comp 100 cs[j]! as[p]!
        let i := idx.getD (pack 7 y) 0
        if !seen[i]! then
          seen := seen.set! i true
          rs := rs.set! i (j + 64 * p + 4096 * (rs[p]! / 4096 + 1))
          q := q.push i
      h := h + 1
    return rs

end CertificateChecks.KernelHSMcLFive

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHSMcLFive.H0X CFSG.RankThree.Native.hs100Case0Hex
#kmisc_hexflat CertificateChecks.KernelHSMcLFive.H0X CFSG.RankThree.Native.hs100Case0Hex 3 100 7 15
#ks_chars CertificateChecks.KernelHSMcLFive.H2X CFSG.RankThree.Native.hs100Case2Hex
#kmisc_hexflat CertificateChecks.KernelHSMcLFive.H2X CFSG.RankThree.Native.hs100Case2Hex 3 100 7 15
#ks_chars CertificateChecks.KernelHSMcLFive.H23X CFSG.RankThree.Native.hs100Case23Hex
#kmisc_hexflat CertificateChecks.KernelHSMcLFive.H23X CFSG.RankThree.Native.hs100Case23Hex 3 100 7
  13

#ks_rawchain CertificateChecks.KernelHSMcLFive.H0 100 7 100 CFSG.RankThree.Native.hs100Case0Arrs
  CFSG.RankThree.Native.hs100Case0BaseArr 3 CertificateChecks.KernelHSMcLFive.d0
#ks_rawchain CertificateChecks.KernelHSMcLFive.H2 100 7 100 CFSG.RankThree.Native.hs100Case2Arrs
  CFSG.RankThree.Native.hs100Case2BaseArr 3 CertificateChecks.KernelHSMcLFive.d2
#ks_rawchain CertificateChecks.KernelHSMcLFive.H23 100 7 100 CFSG.RankThree.Native.hs100Case23Arrs
  CFSG.RankThree.Native.hs100Case23BaseArr 3 CertificateChecks.KernelHSMcLFive.d23

#kb3_enum CertificateChecks.KernelHSMcLFive.EQ CFSG.RankThree.Native.hs100FiveQGens
  CFSG.RankThree.Native.hs100RBaseArr 100 7
#kb3_enum CertificateChecks.KernelHSMcLFive.EA0 CFSG.RankThree.Native.hs100FiveA0Gens
  CFSG.RankThree.Native.hs100RBaseArr 100 7
#kb3_enum CertificateChecks.KernelHSMcLFive.EA23 CFSG.RankThree.Native.hs100FiveA23Gens
  CFSG.RankThree.Native.hs100RBaseArr 100 7
#kb3_enum CertificateChecks.KernelHSMcLFive.ED CertificateChecks.KernelHSMcLFive.dGensM
  CFSG.RankThree.Native.hs100RBaseArr 100 7

#kmisc_packarrs CertificateChecks.KernelHSMcLFive.WT CertificateChecks.KernelHSMcLFive.wtM 16
