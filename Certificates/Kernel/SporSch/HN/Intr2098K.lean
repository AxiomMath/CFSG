
module

public import Certificates.Kernel.SporSch.HN.StrongK
public import CFSG.Sporadic.HNSchreier.IntrinsicData
public import CFSG.Sporadic.HNSchreier.FAData
meta import CFSG.Sporadic.HNSchreier.InvolCheckInputs
meta import CFSG.Sporadic.HNSchreier.IntrinsicData
meta import CFSG.Sporadic.HNSchreier.FAData
public meta import Certificates.Data.Kernel.SporSch.HNStrongData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNIntr

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier

@[expose] def letE (l : Int) : Nat := if 0 < l then l.toNat - 1 else 16 + (-l).toNat

@[expose] def seedE (l : Nat) : Nat := if l = 1 then 34 else 35

@[expose] def uSylE (l : Nat) : Nat :=
  if l = 1 then 34 else if l = 2 then 35 else if l = 3 then 37 else 38

@[expose] def uSylW (l : Nat) : List Nat := if l = 3 then [1, 2] else if l = 4 then [1, 2, 2] else [l]

@[expose] def wRootS : Array (List Nat) :=
  #[[4, 3, 3, 4, 4, 4, 3, 4, 4, 3, 3, 3, 3, 3, 4, 3, 3], [2, 4, 4, 4, 3, 3, 3, 3, 4]]

@[expose] def chXY : Nat := 36

@[expose] def chS : Nat := 39

@[expose] def chH (c : Nat) : Nat := chS + FAData.sWords[0]!.length +
  if c = 0 then 0 else IntrinsicData.wHWord[0]!.length

@[expose] def chU (c : Nat) : Nat := chH 1 + IntrinsicData.wHWord[1]!.length +
  if c = 0 then 0 else wRootS[0]!.length

@[expose] def pX (c : Nat) : Nat := chU 1 + wRootS[1]!.length + 2 * c

@[expose] def pY (c : Nat) : Nat := pX c + 1

meta def letG (l : Int) : Nat := if 0 < l then l.toNat - 1 else 16 + (-l).toNat

meta def seedG (l : Nat) : Nat := if l = 1 then 34 else 35

meta def uSylG (l : Nat) : Nat := if l = 1 then 34 else if l = 2 then 35 else if l = 3 then 37 else 38

meta def uSylParse : List Nat → List Nat
  | 1 :: 2 :: 2 :: r => 4 :: uSylParse r
  | 1 :: 2 :: r => 3 :: uSylParse r
  | l :: r => l :: uSylParse r
  | [] => []

meta def build : List (Array (Array Nat)) × List (Nat × Nat × Nat) := Id.run do
  let m := mulM 5 133
  let st := CFSG.KS.SporSch.hnStrongRows
  let mut M : Array (Array (Array Nat)) := #[]
  let mut sp : Array (Nat × Nat × Nat) := #[]
  for j in [0:34] do
    M := M.push (st.getD j #[])
    sp := sp.push (2, 0, 0)
  M := M.push rowsA
  sp := sp.push (2, 0, 0)
  M := M.push rowsB
  sp := sp.push (2, 0, 0)
  let seedChain (M0 : Array (Array (Array Nat))) (sp0 : Array (Nat × Nat × Nat))
      (E : Nat → Nat) (w : List Nat) : Array (Array (Array Nat)) × Array (Nat × Nat × Nat) :=
      Id.run do
    let mut M := M0
    let mut sp := sp0
    let mut cur := M.size
    M := M.push (M.getD (E (w.headD 0)) #[])
    sp := sp.push (1, E (w.headD 0), 0)
    for l in w.drop 1 do
      M := M.push (m (M.getD cur #[]) (M.getD (E l) #[]))
      sp := sp.push (0, cur, E l)
      cur := M.size - 1
    return (M, sp)
  (M, sp) := seedChain M sp seedG [1, 2, 2]
  let strongChain (M0 : Array (Array (Array Nat))) (sp0 : Array (Nat × Nat × Nat))
      (w : List Int) : Array (Array (Array Nat)) × Array (Nat × Nat × Nat) := Id.run do
    let wr := w.reverse
    let mut M := M0
    let mut sp := sp0
    let mut cur := M.size
    M := M.push (M.getD (letG (wr.headD 0)) #[])
    sp := sp.push (1, letG (wr.headD 0), 0)
    for l in wr.drop 1 do
      M := M.push (m (M.getD (letG l) #[]) (M.getD cur #[]))
      sp := sp.push (0, letG l, cur)
      cur := M.size - 1
    return (M, sp)
  (M, sp) := strongChain M sp (FAData.sWords.getD 0 [])
  let s1 := M.size - 1
  (M, sp) := strongChain M sp (IntrinsicData.wHWord.getD 0 [])
  let h0 := M.size - 1
  (M, sp) := strongChain M sp (IntrinsicData.wHWord.getD 1 [])
  let h1 := M.size - 1
  (M, sp) := seedChain M sp uSylG (uSylParse (IntrinsicData.wRoot.getD 0 []))
  let u0 := M.size - 1
  (M, sp) := seedChain M sp uSylG (uSylParse (IntrinsicData.wRoot.getD 1 []))
  let u1 := M.size - 1
  M := M.push (m (M.getD s1 #[]) (M.getD u0 #[]))
  sp := sp.push (0, s1, u0)
  M := M.push (m (M.getD u0 #[]) (M.getD h0 #[]))
  sp := sp.push (0, u0, h0)
  M := M.push (m (M.getD s1 #[]) (M.getD u1 #[]))
  sp := sp.push (0, s1, u1)
  M := M.push (m (M.getD u1 #[]) (M.getD h1 #[]))
  sp := sp.push (0, u1, h1)
  return (M.toList, sp.toList)

meta def specOnly : List (Nat × Nat × Nat) := Id.run do
  let mut sp : Array (Nat × Nat × Nat) := #[]
  for _ in [0:36] do
    sp := sp.push (2, 0, 0)
  sp := sp ++ #[(1, 34, 0), (0, 36, 35), (0, 37, 35)]
  let mut ends : Array Nat := #[]
  for w in [FAData.sWords.getD 0 [], IntrinsicData.wHWord.getD 0 [],
      IntrinsicData.wHWord.getD 1 []] do
    let wr := w.reverse
    sp := sp.push (1, letG (wr.headD 0), 0)
    for l in wr.drop 1 do
      sp := sp.push (0, letG l, sp.size - 1)
    ends := ends.push (sp.size - 1)
  for w0 in [IntrinsicData.wRoot.getD 0 [], IntrinsicData.wRoot.getD 1 []] do
    let w := uSylParse w0
    sp := sp.push (1, uSylG (w.headD 0), 0)
    for l in w.drop 1 do
      sp := sp.push (0, sp.size - 1, uSylG l)
    ends := ends.push (sp.size - 1)
  let (s1, h0, h1, u0, u1) := (ends[0]!, ends[1]!, ends[2]!, ends[3]!, ends[4]!)
  return (sp ++ #[(0, s1, u0), (0, u0, h0), (0, s1, u1), (0, u1, h1)]).toList

meta def mats : List (Array (Array Nat)) := build.1

meta def spec : List (Nat × Nat × Nat) := specOnly

end CertificateChecks.KernelSporSch.HNIntr

#kss_f5tree CertificateChecks.KernelSporSch.HNC CertificateChecks.KernelSporSch.HNIntr.mats
  CertificateChecks.KernelSporSch.HNIntr.spec

namespace CertificateChecks.KernelSporSch.HNIntr

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier
open CertificateChecks.KernelSporSch

@[expose] noncomputable def sc (k i : Nat) : Nat := slice5 HNC.MT k i

theorem pos_eq : chS = 39 ∧ chH 0 = 49 ∧ chH 1 = 62 ∧ chU 0 = 74 ∧ chU 1 = 91 ∧ pX 0 = 100 ∧
    pY 0 = 101 ∧ pX 1 = 102 ∧ pY 1 = 103 := by decide +kernel

theorem eqS : allN 34 (fun j => allN 133 (fun i =>
    Nat.beq (sc j i) (HNStrong.ss (Nat.add 13 j) i))) = true := by quickRfl
theorem eqA : allN 133 (fun i => Nat.beq (sc 34 i) (HNStrong.ss 0 i)) = true := by quickRfl
theorem eqB : allN 133 (fun i => Nat.beq (sc 35 i) (HNStrong.ss 1 i)) = true := by quickRfl

theorem blk0 : krBlk HNC.MT HNC.OP HNC.L HNC.R 0 36 = true := by quickRfl
theorem blk1 : krBlk HNC.MT HNC.OP HNC.L HNC.R 36 10 = true := by quickRfl
theorem blk2 : krBlk HNC.MT HNC.OP HNC.L HNC.R 46 10 = true := by quickRfl
theorem blk3 : krBlk HNC.MT HNC.OP HNC.L HNC.R 56 10 = true := by quickRfl
theorem blk4 : krBlk HNC.MT HNC.OP HNC.L HNC.R 66 10 = true := by quickRfl
theorem blk5 : krBlk HNC.MT HNC.OP HNC.L HNC.R 76 10 = true := by quickRfl
theorem blk6 : krBlk HNC.MT HNC.OP HNC.L HNC.R 86 10 = true := by quickRfl
theorem blk7 : krBlk HNC.MT HNC.OP HNC.L HNC.R 96 8 = true := by quickRfl

theorem specLt : allN 104 (fun k => bAnd(Nat.blt (HNC.L k) 104, Nat.blt (HNC.R k) 104)) = true := by
  quickRfl

theorem prod_spec : HNC.OP 100 = 0 ∧ HNC.L 100 = 48 ∧ HNC.R 100 = 90 ∧ HNC.OP 101 = 0 ∧
    HNC.L 101 = 90 ∧ HNC.R 101 = 61 ∧ HNC.OP 102 = 0 ∧ HNC.L 102 = 48 ∧ HNC.R 102 = 99 ∧
    HNC.OP 103 = 0 ∧ HNC.L 103 = 99 ∧ HNC.R 103 = 73 := by decide +kernel

theorem eqXY0 : allN 133 (fun i => Nat.beq (sc 100 i) (sc 101 i)) = true := by quickRfl
theorem eqXY1 : allN 133 (fun i => Nat.beq (sc 102 i) (sc 103 i)) = true := by quickRfl

theorem neg_XY : Bool.not (allN 133 (fun i => Nat.beq (sc 100 i) (sc 103 i))) = true := by
  quickRfl
theorem neg_S : Bool.not (allN 133 (fun i => Nat.beq (sc 0 i) (HNStrong.ss 14 i))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNIntr

end
