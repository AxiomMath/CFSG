module

public import Certificates.Kernel.SporSch.HN.GenF5T
public import Certificates.Kernel.SporSch.HN.StrongK
public import Certificates.Data.Kernel.SporSch.HNF5Rank
public import CFSG.Sporadic.HNOddCore.RkCheckInputs
meta import CFSG.Sporadic.HNOddCore.RkCheckInputs
meta import CFSG.Sporadic.HNOddCore.RankData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HNI1P CFSG.Sporadic.HNOddCore.RankData.rankT2P
#ks_chars CertificateChecks.KernelSpor.HNI1Pi CFSG.Sporadic.HNOddCore.RankData.rankT2Pi
#ks_chars CertificateChecks.KernelSpor.HNI1Q CFSG.Sporadic.HNOddCore.RankData.rankT2Q
#ks_chars CertificateChecks.KernelSpor.HNI1Qi CFSG.Sporadic.HNOddCore.RankData.rankT2Qi
#ks_chars CertificateChecks.KernelSpor.HNI2P CFSG.Sporadic.HNOddCore.RankData.rankT4P
#ks_chars CertificateChecks.KernelSpor.HNI2Pi CFSG.Sporadic.HNOddCore.RankData.rankT4Pi
#ks_chars CertificateChecks.KernelSpor.HNI2Q CFSG.Sporadic.HNOddCore.RankData.rankT4Q
#ks_chars CertificateChecks.KernelSpor.HNI2Qi CFSG.Sporadic.HNOddCore.RankData.rankT4Qi
#ks_chars CertificateChecks.KernelSpor.HNI3P CFSG.Sporadic.HNOddCore.RankData.rankT6P
#ks_chars CertificateChecks.KernelSpor.HNI3Pi CFSG.Sporadic.HNOddCore.RankData.rankT6Pi
#ks_chars CertificateChecks.KernelSpor.HNI3Q CFSG.Sporadic.HNOddCore.RankData.rankT6Q
#ks_chars CertificateChecks.KernelSpor.HNI3Qi CFSG.Sporadic.HNOddCore.RankData.rankT6Qi

namespace CertificateChecks.KernelSpor.HN2090

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore

meta def letR (l : Int) : Nat := if 0 < l then l.toNat - 1 else 16 + (-l).toNat

meta def build : List (Array (Array Nat)) × List (Nat × Nat × Nat) := Id.run do
  let m := mulM 5 133
  let st := CertificateChecks.KernelSporSch.HNStrong.mats.toArray
  let mut M : Array (Array (Array Nat)) := #[]
  let mut sp : Array (Nat × Nat × Nat) := #[]
  for j in [0:17] do
    M := M.push st[13 + j]!
    sp := sp.push (2, 0, 0)
  for j in [0:17] do
    M := M.push st[30 + j]!
    sp := sp.push (2, 0, 0)
  let mut ends : Array Nat := #[]
  for w0 in [InvData.t2Word, InvData.t4Word] do
    let w := w0.reverse
    let mut cur := M.size
    M := M.push (M[letR w[0]!]!)
    sp := sp.push (1, letR w[0]!, 0)
    for l in w.drop 1 do
      M := M.push (m (M[letR l]!) (M[cur]!))
      sp := sp.push (0, letR l, cur)
      cur := M.size - 1
    ends := ends.push cur
  M := M.push rowsA
  sp := sp.push (2, 0, 0)
  ends := ends.push (M.size - 1)
  for k in [0:3] do
    let c := invRankRows[k]!
    let b := M.size
    for t in [0:4] do
      M := M.push (c.getD t #[])
      sp := sp.push (2, 0, 0)
    M := M.push (subId (M[ends[k]!]!))
    sp := sp.push (2, 0, 0)
    let c0 := c.getD 0 #[]
    let c1 := c.getD 1 #[]
    let c2 := c.getD 2 #[]
    let c3 := c.getD 3 #[]
    M := M.push (m c0 c1)
    sp := sp.push (0, b, b + 1)
    M := M.push (m c2 c3)
    sp := sp.push (0, b + 2, b + 3)
    M := M.push (m c0 (M.getD (b + 4) #[]))
    sp := sp.push (0, b, b + 4)
    M := M.push (m (M.getD (b + 7) #[]) c2)
    sp := sp.push (0, b + 7, b + 2)
  return (M.toList, sp.toList)

meta def mats : List (Array (Array Nat)) := build.1

meta def spec : List (Nat × Nat × Nat) := build.2

end CertificateChecks.KernelSpor.HN2090

#kss_f5tree CertificateChecks.KernelSpor.HNI CertificateChecks.KernelSpor.HN2090.mats
  CertificateChecks.KernelSpor.HN2090.spec

namespace CertificateChecks.KernelSpor.HN2090

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor

@[expose] noncomputable def sr (k i : Nat) : Nat := slice5 HNI.MT k i

theorem eqS : allN 17 (fun j => allN 133 (fun i =>
    Nat.beq (sr j i) (HNStrong.ss (Nat.add 13 j) i))) = true := by quickRfl
theorem eqSi : allN 17 (fun j => allN 133 (fun i =>
    Nat.beq (sr (Nat.add 17 j) i) (HNStrong.ss (Nat.add 30 j) i))) = true := by quickRfl
theorem eqA : allN 133 (fun i => Nat.beq (sr 62 i) (HNStrong.ss 0 i)) = true := by quickRfl

theorem blk0 : krBlk HNI.MT HNI.OP HNI.L HNI.R 0 35 = true := by quickRfl
theorem blk1 : krBlk HNI.MT HNI.OP HNI.L HNI.R 35 9 = true := by quickRfl
theorem blk2 : krBlk HNI.MT HNI.OP HNI.L HNI.R 44 8 = true := by quickRfl
theorem blk3 : krBlk HNI.MT HNI.OP HNI.L HNI.R 52 11 = true := by quickRfl
theorem blk4 : krBlk HNI.MT HNI.OP HNI.L HNI.R 63 14 = true := by quickRfl
theorem blk5 : krBlk HNI.MT HNI.OP HNI.L HNI.R 77 13 = true := by quickRfl

theorem p1P : pay5K (sr 63) HNI1P.chars = true := by quickRfl
theorem p1Pi : pay5K (sr 64) HNI1Pi.chars = true := by quickRfl
theorem p1Q : pay5K (sr 65) HNI1Q.chars = true := by quickRfl
theorem p1Qi : pay5K (sr 66) HNI1Qi.chars = true := by quickRfl
theorem p2P : pay5K (sr 72) HNI2P.chars = true := by quickRfl
theorem p2Pi : pay5K (sr 73) HNI2Pi.chars = true := by quickRfl
theorem p2Q : pay5K (sr 74) HNI2Q.chars = true := by quickRfl
theorem p2Qi : pay5K (sr 75) HNI2Qi.chars = true := by quickRfl
theorem p3P : pay5K (sr 81) HNI3P.chars = true := by quickRfl
theorem p3Pi : pay5K (sr 82) HNI3Pi.chars = true := by quickRfl
theorem p3Q : pay5K (sr 83) HNI3Q.chars = true := by quickRfl
theorem p3Qi : pay5K (sr 84) HNI3Qi.chars = true := by quickRfl

theorem sub1 : allN 133 (fun i => Nat.beq (sr 67 i) (subRow5 (sr 51) i)) = true := by quickRfl
theorem sub2 : allN 133 (fun i => Nat.beq (sr 76 i) (subRow5 (sr 61) i)) = true := by quickRfl
theorem sub3 : allN 133 (fun i => Nat.beq (sr 85 i) (subRow5 (sr 62) i)) = true := by quickRfl

theorem idP1 : allN 133 (fun i => Nat.beq (sr 68 i) (idRow5 i)) = true := by quickRfl
theorem idQ1 : allN 133 (fun i => Nat.beq (sr 69 i) (idRow5 i)) = true := by quickRfl
theorem idP2 : allN 133 (fun i => Nat.beq (sr 77 i) (idRow5 i)) = true := by quickRfl
theorem idQ2 : allN 133 (fun i => Nat.beq (sr 78 i) (idRow5 i)) = true := by quickRfl
theorem idP3 : allN 133 (fun i => Nat.beq (sr 86 i) (idRow5 i)) = true := by quickRfl
theorem idQ3 : allN 133 (fun i => Nat.beq (sr 87 i) (idRow5 i)) = true := by quickRfl

theorem dg1 : allN 133 (fun i => Nat.beq (sr 71 i) (diagRow5 56 i)) = true := by quickRfl
theorem dg2 : allN 133 (fun i => Nat.beq (sr 80 i) (diagRow5 64 i)) = true := by quickRfl
theorem dg3 : allN 133 (fun i => Nat.beq (sr 89 i) (diagRow5 56 i)) = true := by quickRfl

end CertificateChecks.KernelSpor.HN2090

end
