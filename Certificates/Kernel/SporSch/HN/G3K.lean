module

public import Certificates.Kernel.SporSch.HN.GenF5T
public import Certificates.Kernel.SporSch.HN.StrongK
public meta import Certificates.Data.HNG3Order
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNG3

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier

meta def letR (l : Nat) : Nat := if l = 1 then 0 else 1

meta def letH (l : Int) : Nat := if 0 < l then 2 + l.toNat else 19 + (-l).toNat

meta def build : List (Array (Array Nat)) × List (Nat × Nat × Nat) := Id.run do
  let m := mulM 5 133
  let regs := progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram
  let hs := extendStrongM #[regs[1]!, regs[2]!] LocalData.strongWords
  let mut M : Array (Array (Array Nat)) := #[rowsA, rowsB, idM 133]
  for j in [0:17] do
    M := M.push hs.1[j]!
  for j in [0:17] do
    M := M.push hs.2[j]!
  let mut sp : Array (Nat × Nat × Nat) := Array.replicate M.size (2, 0, 0)
  let w := FAData.g3Root
  M := M.push M[letR w[0]!]!
  sp := sp.push (1, letR w[0]!, 0)
  for l in w.drop 1 do
    M := M.push (m M[M.size - 1]! M[letR l]!)
    sp := sp.push (0, M.size - 2, letR l)
  let qEnd := M.size - 1
  let h := FAData.g3H.reverse
  M := M.push M[letH h[0]!]!
  sp := sp.push (1, letH h[0]!, 0)
  for l in h.drop 1 do
    M := M.push (m M[letH l]! M[M.size - 1]!)
    sp := sp.push (0, letH l, M.size - 2)
  let hEnd := M.size - 1
  M := M.push (m M[qEnd]! M[hEnd]!)
  sp := sp.push (0, qEnd, hEnd)
  let gI := M.size - 1
  M := M.push M[gI]!
  sp := sp.push (1, gI, 0)
  for _ in [0:2] do
    M := M.push (m M[M.size - 1]! M[gI]!)
    sp := sp.push (0, M.size - 2, gI)
  let wI := M.size - 1
  M := M.push M[wI]!
  sp := sp.push (1, wI, 0)
  for _ in [0:9] do
    M := M.push (m M[M.size - 1]! M[wI]!)
    sp := sp.push (0, M.size - 2, wI)
  return (M.toList, sp.toList)

meta def mats : List (Array (Array Nat)) := build.1

meta def spec : List (Nat × Nat × Nat) := build.2

end CertificateChecks.KernelSporSch.HNG3

#kss_f5tree CertificateChecks.KernelSporSch.HNG CertificateChecks.KernelSporSch.HNG3.mats
  CertificateChecks.KernelSporSch.HNG3.spec

namespace CertificateChecks.KernelSporSch.HNG3

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch
open CertificateChecks.KernelSporSch

@[expose] noncomputable def sg (k i : Nat) : Nat := slice5 HNG.MT k i

theorem tieA : allN 133 (fun i => Nat.beq (sg 0 i) (HNStrong.ss 0 i)) = true := by quickRfl
theorem tieB : allN 133 (fun i => Nat.beq (sg 1 i) (HNStrong.ss 1 i)) = true := by quickRfl
theorem tieI : allN 133 (fun i => Nat.beq (sg 2 i) (idRow5 i)) = true := by quickRfl

theorem tieF : allN 17 (fun j => allN 133 (fun i =>
    Nat.beq (sg (Nat.add 3 j) i) (HNStrong.ss (Nat.add 13 j) i))) = true := by quickRfl

theorem tieFI : allN 17 (fun j => allN 133 (fun i =>
    Nat.beq (sg (Nat.add 20 j) i) (HNStrong.ss (Nat.add 30 j) i))) = true := by quickRfl

theorem blk0 : krBlk HNG.MT HNG.OP HNG.L HNG.R 0 37 = true := by quickRfl
theorem blk1 : krBlk HNG.MT HNG.OP HNG.L HNG.R 37 10 = true := by quickRfl
theorem blk2 : krBlk HNG.MT HNG.OP HNG.L HNG.R 47 10 = true := by quickRfl
theorem blk3 : krBlk HNG.MT HNG.OP HNG.L HNG.R 57 10 = true := by quickRfl
theorem blk4 : krBlk HNG.MT HNG.OP HNG.L HNG.R 67 10 = true := by quickRfl
theorem blk5 : krBlk HNG.MT HNG.OP HNG.L HNG.R 77 9 = true := by quickRfl

theorem specLt : allN 86 (fun k => bAnd(Nat.blt (HNG.L k) 86, Nat.blt (HNG.R k) 86)) = true := by
  quickRfl

theorem id85 : allN 133 (fun i => Nat.beq (sg 85 i) (idRow5 i)) = true := by quickRfl

theorem ne80 : (!Nat.beq (sg 80 0) (idRow5 0)) = true := by quickRfl

theorem ne77 : (!Nat.beq (sg 77 0) (idRow5 0)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNG3

end
