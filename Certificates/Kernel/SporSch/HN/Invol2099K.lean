
module

public import Certificates.Kernel.SporSch.HN.StrongK
public import Certificates.Kernel.SporSch.HN.Invol2099U
public import Certificates.Data.Kernel.SporSch.HNF5Inv
public import Certificates.Data.Kernel.SporSch.HNF5Mod
public import Certificates.Data.Kernel.SporSch.HNF5KronT
public import Certificates.Kernel.SporSch.HN.GenF5T
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
meta import CFSG.Sporadic.HNSchreier.InvolCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNInvol

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier

meta def rowsMat (vs : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 133) fun i => vs.getD i.val (Array.replicate 133 0)

meta def build : List (Array (Array Nat)) × List (Nat × Nat × Nat) := Id.run do
  let m := mulM 5 133
  let st := HNStrong.mats.toArray
  let A := rowsA
  let B := rowsB
  let mut M : Array (Array (Array Nat)) := #[A, B, colsMat 133 A, colsMat 133 B]
  let mut sp : Array (Nat × Nat × Nat) := #[(2, 0, 0), (2, 0, 0), (3, 0, 0), (3, 1, 0)]
  for j in [0:17] do
    M := M.push (st.getD (13 + j) #[])
    sp := sp.push (2, 0, 0)
  M := M.push (colsMat 133 (M.getD 4 #[]))
  sp := sp.push (3, 4, 0)
  M := M.push (colsMat 133 (M.getD 5 #[]))
  sp := sp.push (3, 5, 0)
  let wi := LocalData.innerWord.reverse.map Int.toNat
  M := M.push (M.getD (3 + wi.headD 0) #[])
  sp := sp.push (1, 3 + wi.headD 0, 0)
  for l in wi.drop 1 do
    M := M.push (m (M.getD (3 + l) #[]) (M.getD (M.size - 1) #[]))
    sp := sp.push (0, 3 + l, M.size - 2)
  let Ui := HNInvolU.mats.getD 60 #[]
  let S := rowsOf 5 133 LocalData.normalizerPayload
  let C := rowsOf 5 133 LocalData.involutionPayload
  let D := M.getD 33 #[]
  M := M.push Ui
  sp := sp.push (2, 0, 0)
  M := M.push S
  sp := sp.push (2, 0, 0)
  M := M.push C
  sp := sp.push (2, 0, 0)
  M := M.push (m D Ui)
  sp := sp.push (0, 33, 34)
  M := M.push (m (m D Ui) S)
  sp := sp.push (0, 37, 35)
  M := M.push (m C C)
  sp := sp.push (0, 36, 36)
  M := M.push (colsMat 133 C)
  sp := sp.push (3, 36, 0)
  M := M.push (m S A)
  sp := sp.push (0, 35, 0)
  M := M.push (m A S)
  sp := sp.push (0, 0, 35)
  M := M.push (m B B)
  sp := sp.push (0, 1, 1)
  let ABB := m A (m B B)
  M := M.push ABB
  sp := sp.push (0, 0, 43)
  M := M.push ABB
  sp := sp.push (1, 44, 0)
  for _ in [0:7] do
    M := M.push (m (M.getD (M.size - 1) #[]) ABB)
    sp := sp.push (0, M.size - 2, 44)
  let W := M.getD 52 #[]
  M := M.push (m S B)
  sp := sp.push (0, 35, 1)
  M := M.push (m W (m S B))
  sp := sp.push (0, 52, 53)
  M := M.push (m W S)
  sp := sp.push (0, 52, 35)
  M := M.push (m B (m W S))
  sp := sp.push (0, 1, 55)
  let rw := LocalData.rootWord
  let mut ys : Array (Array Nat) := #[rootVec]
  for t in [0:rw.length] do
    let l := rw.getD (rw.length - 1 - t) 0
    ys := ys.push (mulVec 5 133 (seedSel A B l) (ys.getD t #[]))
  M := M.push (rowsMat ys)
  sp := sp.push (2, 0, 0)
  let regs := progRegsM (initRegsM A B) Data.subgroupProgram
  let hs := extendStrongM #[regs.getD 1 #[], regs.getD 2 #[]] LocalData.strongWords
  let xs := xVecs hs.1 (ys.getD rw.length #[]) LocalData.parents
  for c in [0:4] do
    M := M.push (rowsMat (xs.extract (133 * c) (133 * c + 133)))
    sp := sp.push (2, 0, 0)
  return (M.toList, sp.toList)

meta def mats : List (Array (Array Nat)) := build.1

meta def spec : List (Nat × Nat × Nat) := build.2

end CertificateChecks.KernelSporSch.HNInvol

#kss_f5tree CertificateChecks.KernelSporSch.HNI CertificateChecks.KernelSporSch.HNInvol.mats
  CertificateChecks.KernelSporSch.HNInvol.spec

namespace CertificateChecks.KernelSporSch.HNInvol

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier
open CertificateChecks.KernelSporSch

@[expose] noncomputable def sx (k i : Nat) : Nat := slice5 HNI.MT k i

@[expose] noncomputable def ltT (l : Nat) : Nat := nIf(Nat.beq l 1, 2, 3)

theorem eqA : allN 133 (fun i => Nat.beq (sx 0 i) (HNStrong.ss 0 i)) = true := by quickRfl
theorem eqB : allN 133 (fun i => Nat.beq (sx 1 i) (HNStrong.ss 1 i)) = true := by quickRfl
theorem eqH : allN 17 (fun j => allN 133 (fun i =>
    Nat.beq (sx (Nat.add 4 j) i) (HNStrong.ss (Nat.add 13 j) i))) = true := by quickRfl
theorem eqUi : allN 133 (fun i => Nat.beq (sx 34 i) (HNInvolU.su 60 i)) = true := by quickRfl

theorem blk0 : krBlkT HNI.MT HNI.OP HNI.L HNI.R 0 11 = true := by quickRfl
theorem blk1 : krBlkT HNI.MT HNI.OP HNI.L HNI.R 11 10 = true := by quickRfl
theorem blk2 : krBlkT HNI.MT HNI.OP HNI.L HNI.R 21 10 = true := by quickRfl
theorem blk3 : krBlkT HNI.MT HNI.OP HNI.L HNI.R 31 10 = true := by quickRfl
theorem blk4 : krBlkT HNI.MT HNI.OP HNI.L HNI.R 41 10 = true := by quickRfl
theorem blk5 : krBlkT HNI.MT HNI.OP HNI.L HNI.R 51 11 = true := by quickRfl

theorem specLt : allN 62 (fun k => bAnd(Nat.blt (HNI.L k) 62, Nat.blt (HNI.R k) 62)) = true := by
  quickRfl

theorem id39 : allN 133 (fun i => Nat.beq (sx 39 i) (idRow5 i)) = true := by quickRfl
theorem e38 : allN 133 (fun i => Nat.beq (sx 38 i) (sx 36 i)) = true := by quickRfl
theorem e41 : allN 133 (fun i => Nat.beq (sx 41 i) (sx 42 i)) = true := by quickRfl
theorem e54 : allN 133 (fun i => Nat.beq (sx 54 i) (sx 56 i)) = true := by quickRfl
theorem ne36 : anyN 133 (fun i => Bool.not (Nat.beq (sx 36 i) (idRow5 i))) = true := by quickRfl

theorem fixv : Nat.beq (vm5 (sx 40) (sx 57 0)) (sx 57 0) = true := by quickRfl
theorem rchain : vecChain5 HNI.MT 57 ltT LocalData.rootWord = true := by quickRfl
theorem x0 : Nat.beq (sx 58 0) (sx 57 40) = true := by quickRfl
theorem xrec0 : allBlk 1 (recRow5 HNI.MT 58 21 22 LocalData.parents) 230 = true := by quickRfl
theorem xrec1 : allBlk 231 (recRow5 HNI.MT 58 21 22 LocalData.parents) 231 = true := by quickRfl

end CertificateChecks.KernelSporSch.HNInvol

end
