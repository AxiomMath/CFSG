module

public import Certificates.Kernel.SporSch.HN.GenF5T
public import Certificates.Kernel.SporSch.HN.StrongK
public import Certificates.Data.Kernel.SporSch.HNF5Rank
public import CFSG.Sporadic.HNSchreier.RankCheckInputs
meta import CFSG.Sporadic.HNSchreier.RankCheckInputs
meta import CFSG.Sporadic.HNSchreier.RankData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.HNR1P CFSG.Sporadic.HNSchreier.RankData.rank1P
#ks_chars CertificateChecks.KernelSporSch.HNR1Pi CFSG.Sporadic.HNSchreier.RankData.rank1Pi
#ks_chars CertificateChecks.KernelSporSch.HNR1Q CFSG.Sporadic.HNSchreier.RankData.rank1Q
#ks_chars CertificateChecks.KernelSporSch.HNR1Qi CFSG.Sporadic.HNSchreier.RankData.rank1Qi
#ks_chars CertificateChecks.KernelSporSch.HNR2P CFSG.Sporadic.HNSchreier.RankData.rank2P
#ks_chars CertificateChecks.KernelSporSch.HNR2Pi CFSG.Sporadic.HNSchreier.RankData.rank2Pi
#ks_chars CertificateChecks.KernelSporSch.HNR2Q CFSG.Sporadic.HNSchreier.RankData.rank2Q
#ks_chars CertificateChecks.KernelSporSch.HNR2Qi CFSG.Sporadic.HNSchreier.RankData.rank2Qi
#ks_chars CertificateChecks.KernelSporSch.HNR3P CFSG.Sporadic.HNSchreier.RankData.rank3P
#ks_chars CertificateChecks.KernelSporSch.HNR3Pi CFSG.Sporadic.HNSchreier.RankData.rank3Pi
#ks_chars CertificateChecks.KernelSporSch.HNR3Q CFSG.Sporadic.HNSchreier.RankData.rank3Q
#ks_chars CertificateChecks.KernelSporSch.HNR3Qi CFSG.Sporadic.HNSchreier.RankData.rank3Qi
#ks_chars CertificateChecks.KernelSporSch.HNR4P CFSG.Sporadic.HNSchreier.RankData.rank4P
#ks_chars CertificateChecks.KernelSporSch.HNR4Pi CFSG.Sporadic.HNSchreier.RankData.rank4Pi
#ks_chars CertificateChecks.KernelSporSch.HNR4Q CFSG.Sporadic.HNSchreier.RankData.rank4Q
#ks_chars CertificateChecks.KernelSporSch.HNR4Qi CFSG.Sporadic.HNSchreier.RankData.rank4Qi

namespace CertificateChecks.KernelSporSch.HNRank

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier

meta def letR (l : Int) : Nat := if 0 < l then l.toNat - 1 else 16 + (-l).toNat

meta def build : List (Array (Array Nat)) × List (Nat × Nat × Nat) := Id.run do
  let m := mulM 5 133
  let st := HNStrong.mats.toArray
  let mut M : Array (Array (Array Nat)) := #[]
  let mut sp : Array (Nat × Nat × Nat) := #[]
  for j in [0:17] do
    M := M.push st[13 + j]!
    sp := sp.push (2, 0, 0)
  for j in [0:17] do
    M := M.push st[30 + j]!
    sp := sp.push (2, 0, 0)
  let mut ends : Array Nat := #[]
  for k in [0:4] do
    let w := FAData.sWords[k]!.reverse
    let mut cur := M.size
    M := M.push (M[letR w[0]!]!)
    sp := sp.push (1, letR w[0]!, 0)
    for l in w.drop 1 do
      M := M.push (m (M[letR l]!) (M[cur]!))
      sp := sp.push (0, letR l, cur)
      cur := M.size - 1
    ends := ends.push cur
  for k in [0:4] do
    let c := rankCertRows[k]!
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

end CertificateChecks.KernelSporSch.HNRank

#kss_f5tree CertificateChecks.KernelSporSch.HNR CertificateChecks.KernelSporSch.HNRank.mats
  CertificateChecks.KernelSporSch.HNRank.spec

namespace CertificateChecks.KernelSporSch.HNRank

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch
open CertificateChecks.KernelSporSch

@[expose] noncomputable def sr (k i : Nat) : Nat := slice5 HNR.MT k i

theorem eqS : allN 17 (fun j => allN 133 (fun i =>
    Nat.beq (sr j i) (HNStrong.ss (Nat.add 13 j) i))) = true := by quickRfl
theorem eqSi : allN 17 (fun j => allN 133 (fun i =>
    Nat.beq (sr (Nat.add 17 j) i) (HNStrong.ss (Nat.add 30 j) i))) = true := by quickRfl

theorem blk0 : krBlk HNR.MT HNR.OP HNR.L HNR.R 0 35 = true := by quickRfl
theorem blk1 : krBlk HNR.MT HNR.OP HNR.L HNR.R 35 13 = true := by quickRfl
theorem blk2 : krBlk HNR.MT HNR.OP HNR.L HNR.R 48 13 = true := by quickRfl
theorem blk3 : krBlk HNR.MT HNR.OP HNR.L HNR.R 61 9 = true := by quickRfl
theorem blk4 : krBlk HNR.MT HNR.OP HNR.L HNR.R 70 8 = true := by quickRfl
theorem blk5 : krBlk HNR.MT HNR.OP HNR.L HNR.R 78 9 = true := by quickRfl
theorem blk6 : krBlk HNR.MT HNR.OP HNR.L HNR.R 87 9 = true := by quickRfl
theorem blk7 : krBlk HNR.MT HNR.OP HNR.L HNR.R 96 18 = true := by quickRfl
theorem blk8 : krBlk HNR.MT HNR.OP HNR.L HNR.R 114 18 = true := by quickRfl

theorem p1P : pay5K (sr 96) HNR1P.chars = true := by quickRfl
theorem p1Pi : pay5K (sr 97) HNR1Pi.chars = true := by quickRfl
theorem p1Q : pay5K (sr 98) HNR1Q.chars = true := by quickRfl
theorem p1Qi : pay5K (sr 99) HNR1Qi.chars = true := by quickRfl
theorem p2P : pay5K (sr 105) HNR2P.chars = true := by quickRfl
theorem p2Pi : pay5K (sr 106) HNR2Pi.chars = true := by quickRfl
theorem p2Q : pay5K (sr 107) HNR2Q.chars = true := by quickRfl
theorem p2Qi : pay5K (sr 108) HNR2Qi.chars = true := by quickRfl
theorem p3P : pay5K (sr 114) HNR3P.chars = true := by quickRfl
theorem p3Pi : pay5K (sr 115) HNR3Pi.chars = true := by quickRfl
theorem p3Q : pay5K (sr 116) HNR3Q.chars = true := by quickRfl
theorem p3Qi : pay5K (sr 117) HNR3Qi.chars = true := by quickRfl
theorem p4P : pay5K (sr 123) HNR4P.chars = true := by quickRfl
theorem p4Pi : pay5K (sr 124) HNR4Pi.chars = true := by quickRfl
theorem p4Q : pay5K (sr 125) HNR4Q.chars = true := by quickRfl
theorem p4Qi : pay5K (sr 126) HNR4Qi.chars = true := by quickRfl

theorem sub1 : allN 133 (fun i => Nat.beq (sr 100 i) (subRow5 (sr 43) i)) = true := by quickRfl
theorem sub2 : allN 133 (fun i => Nat.beq (sr 109 i) (subRow5 (sr 60) i)) = true := by quickRfl
theorem sub3 : allN 133 (fun i => Nat.beq (sr 118 i) (subRow5 (sr 77) i)) = true := by quickRfl
theorem sub4 : allN 133 (fun i => Nat.beq (sr 127 i) (subRow5 (sr 95) i)) = true := by quickRfl

theorem idP1 : allN 133 (fun i => Nat.beq (sr 101 i) (idRow5 i)) = true := by quickRfl
theorem idQ1 : allN 133 (fun i => Nat.beq (sr 102 i) (idRow5 i)) = true := by quickRfl
theorem idP2 : allN 133 (fun i => Nat.beq (sr 110 i) (idRow5 i)) = true := by quickRfl
theorem idQ2 : allN 133 (fun i => Nat.beq (sr 111 i) (idRow5 i)) = true := by quickRfl
theorem idP3 : allN 133 (fun i => Nat.beq (sr 119 i) (idRow5 i)) = true := by quickRfl
theorem idQ3 : allN 133 (fun i => Nat.beq (sr 120 i) (idRow5 i)) = true := by quickRfl
theorem idP4 : allN 133 (fun i => Nat.beq (sr 128 i) (idRow5 i)) = true := by quickRfl
theorem idQ4 : allN 133 (fun i => Nat.beq (sr 129 i) (idRow5 i)) = true := by quickRfl

theorem dg1 : allN 133 (fun i => Nat.beq (sr 104 i) (diagRow5 84 i)) = true := by quickRfl
theorem dg2 : allN 133 (fun i => Nat.beq (sr 113 i) (diagRow5 84 i)) = true := by quickRfl
theorem dg3 : allN 133 (fun i => Nat.beq (sr 122 i) (diagRow5 90 i)) = true := by quickRfl
theorem dg4 : allN 133 (fun i => Nat.beq (sr 131 i) (diagRow5 84 i)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNRank

end
