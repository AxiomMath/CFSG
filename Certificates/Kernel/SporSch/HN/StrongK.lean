
module

public import Certificates.Kernel.SporSch.HN.GenF5M
public import Certificates.Kernel.SporSch.HN.GenF5T
public import Certificates.Kernel.SporSch.HN.Seeds2106K
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
meta import CFSG.Sporadic.HNSchreier.InvolCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNStrong

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier

meta def letE (l : Int) : Nat := if 0 < l then 12 + l.toNat else 29 + (-l).toNat

meta def build : List (Array (Array Nat)) × List (Nat × Nat × Nat) := Id.run do
  let m := mulM 5 133
  let mut M : Array (Array (Array Nat)) := #[rowsA, rowsB, idM 133]
  let mut sp : Array (Nat × Nat × Nat) := #[(2, 0, 0), (2, 0, 0), (2, 0, 0)]
  let mut reg : Array Nat := #[2, 0, 1, 2, 2, 2, 2, 2, 2, 2, 2]
  for (a, b, c) in Data.subgroupProgram do
    M := M.push (m M[reg[a]!]! M[reg[b]!]!)
    sp := sp.push (0, reg[a]!, reg[b]!)
    reg := reg.set! c (M.size - 1)
  let base := M.size
  for _ in [0:51] do
    M := M.push (idM 133)
    sp := sp.push (2, 0, 0)
  let mut S : Array (Array (Array Nat)) := #[rowsA, M[reg[2]!]!]
  let mut ends : Array Nat := #[0, reg[2]!]
  let mut Si : Array (Array (Array Nat)) := #[invM 5 133 rowsA, invM 5 133 M[reg[2]!]!]
  for j in [2:17] do
    let w := LocalData.strongWords[j]!.reverse
    let mut cur := M.size
    M := M.push (if 0 < w[0]! then S[w[0]!.toNat - 1]! else Si[(-w[0]!).toNat - 1]!)
    sp := sp.push (1, letE w[0]!, 0)
    for l in w.drop 1 do
      let X := if 0 < l then S[l.toNat - 1]! else Si[(-l).toNat - 1]!
      M := M.push (m X M[cur]!)
      sp := sp.push (0, letE l, cur)
      cur := M.size - 1
    S := S.push M[cur]!
    Si := Si.push (invM 5 133 M[cur]!)
    ends := ends.push cur
  for j in [0:17] do
    M := M.set! (base + j) S[j]!
    sp := sp.set! (base + j) (1, ends[j]!, 0)
    M := M.set! (base + 17 + j) Si[j]!
    M := M.set! (base + 34 + j) (m S[j]! Si[j]!)
    sp := sp.set! (base + 34 + j) (0, base + j, base + 17 + j)
  return (M.toList, sp.toList)

meta def mats : List (Array (Array Nat)) := build.1

meta def spec : List (Nat × Nat × Nat) := build.2

end CertificateChecks.KernelSporSch.HNStrong

#kss_f5tree CertificateChecks.KernelSporSch.HNS CertificateChecks.KernelSporSch.HNStrong.mats
  CertificateChecks.KernelSporSch.HNStrong.spec

namespace CertificateChecks.KernelSporSch.HNStrong

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch
open CertificateChecks.KernelSporSch

@[expose] noncomputable def ss (k i : Nat) : Nat := slice5 HNS.MT k i

theorem eqA : allN 133 (fun i => Nat.beq (ss 0 i) (HNSeeds.sl 0 i)) = true := by quickRfl
theorem eqB : allN 133 (fun i => Nat.beq (ss 1 i) (HNSeeds.sl 1 i)) = true := by quickRfl
theorem id2 : allN 133 (fun i => Nat.beq (ss 2 i) (idRow5 i)) = true := by quickRfl

theorem blk0 : krBlk HNS.MT HNS.OP HNS.L HNS.R 0 13 = true := by quickRfl
theorem blk1 : krBlk HNS.MT HNS.OP HNS.L HNS.R 13 34 = true := by quickRfl
theorem blk2 : krBlk HNS.MT HNS.OP HNS.L HNS.R 47 10 = true := by quickRfl
theorem blk3 : krBlk HNS.MT HNS.OP HNS.L HNS.R 57 10 = true := by quickRfl
theorem blk4 : krBlk HNS.MT HNS.OP HNS.L HNS.R 67 10 = true := by quickRfl
theorem blk5 : krBlk HNS.MT HNS.OP HNS.L HNS.R 77 10 = true := by quickRfl
theorem blk6 : krBlk HNS.MT HNS.OP HNS.L HNS.R 87 10 = true := by quickRfl
theorem blk7 : krBlk HNS.MT HNS.OP HNS.L HNS.R 97 10 = true := by quickRfl
theorem blk8 : krBlk HNS.MT HNS.OP HNS.L HNS.R 107 10 = true := by quickRfl
theorem blk9 : krBlk HNS.MT HNS.OP HNS.L HNS.R 117 10 = true := by quickRfl
theorem blk10 : krBlk HNS.MT HNS.OP HNS.L HNS.R 127 6 = true := by quickRfl

theorem specLt : allN 133 (fun k => bAnd(Nat.blt (HNS.L k) 133, Nat.blt (HNS.R k) 133)) = true := by
  quickRfl

theorem ids : allN 17 (fun j => allN 133 (fun i => Nat.beq (ss (Nat.add 47 j) i) (idRow5 i))) =
    true := by quickRfl

end CertificateChecks.KernelSporSch.HNStrong

end
