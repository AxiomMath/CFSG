module

public meta import Certificates.Data.CFSGNative.SectionRank.Elem3
public meta import CFSG.RankThree.Asc83Table.MatCertDefs
public import CFSG.RankThree.Asc83Table.MatCertDefs

public meta section

namespace CFSG.KC.LocalComp.FactsVMeta

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

def ssaIdx (nregs : Nat) (prog : List Op) : Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let mut ops : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0)]
  let mut regs : Array Nat :=
    (Array.range nregs).map fun r => if r == 0 then 0 else if r == 1 then 1 else 2
  let mut out : Array Nat := #[]
  let mulI := fun (ops : Array (Nat × Nat)) (a b : Nat) =>
    match ops.findIdx? (· == (a, b)) with
    | some i => if i ≥ 3 then (ops, i) else (ops.push (a, b), ops.size)
    | none => (ops.push (a, b), ops.size)
  for o in prog do
    match o with
    | .mul i j k =>
      let (o', r) := mulI ops regs[i]! regs[j]!
      ops := o'
      regs := regs.set! k r
      out := out.push r
    | .pow e i k =>
      if e == 0 then
        regs := regs.set! k 2
        out := out.push 2
      else
        let mut res : Option Nat := none
        let mut base := regs[i]!
        let mut e' := e
        while e' > 0 do
          if e' % 2 == 1 then
            match res with
            | none => res := some base
            | some r0 =>
              let (o', r) := mulI ops r0 base
              ops := o'
              res := some r
          e' := e' / 2
          if e' > 0 then
            let (o', r) := mulI ops base base
            ops := o'
            base := r
        regs := regs.set! k res.get!
        out := out.push res.get!
  return (ops, out, regs)

def wordOps (s u : Nat) : Word → List Op
  | [] => [.pow 0 0 s]
  | (r, e) :: w => .pow e r s :: w.flatMap fun (r', e') => [.pow e' r' u, .mul s u s]

def factWords : MFact → Word × Word
  | .ord r e => ([(r, e)], [])
  | .conj g u w => ((g, 1) :: u, w ++ [(g, 1)])
  | .ne w₁ w₂ _ => (w₁, w₂)
  | .eq w₁ w₂ => (w₁, w₂)

def extN (n : Nat) (fs : List MFact) : Nat := n + 1 + 2 * fs.length

def extProg (n : Nat) (prog : List Op) (fs : List MFact) : List Op :=
  prog ++ fs.zipIdx.flatMap fun (f, i) =>
    wordOps (n + 1 + 2 * i) n (factWords f).1 ++ wordOps (n + 2 + 2 * i) n (factWords f).2

def extData (n : Nat) (prog : List Op) (fs : List MFact) : Data :=
  { seedA := "", seedB := "", nregs := extN n fs, prog := extProg n prog fs, outs := [],
    tests := [] }

def targetsA (n : Nat) (prog : List Op) (m : Nat) : Array (Array Nat) :=
  (ssaIdx n (prog.take m)).2.1.map fun t => #[t]

def finalsA (n : Nat) (prog : List Op) (m : Nat) : Array (Array Nat) :=
  (ssaIdx n (prog.take m)).2.2.map fun t => #[t]

def hintsA (n : Nat) (prog : List Op) (fs : List MFact) : Array (Array Nat) :=
  let regs := (ssaIdx (extN n fs) (extProg n prog fs)).2.2
  (Array.range fs.length).map fun i => #[regs[n + 1 + 2 * i]!, regs[n + 2 + 2 * i]!]

end CFSG.KC.LocalComp.FactsVMeta

end
