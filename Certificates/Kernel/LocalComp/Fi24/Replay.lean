module

public import Certificates.Kernel.LocalComp.Fi24.Steps
public import Certificates.Data.Kernel.LocalComp.Replay
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Data.CFSGNative.SectionRank.Fi24prime
meta import Certificates.Kernel.LocalComp.Fi24.Steps
public import Certificates.Data.CFSGNative.SectionRank.Fi24prime

set_option maxRecDepth 100000

namespace CertificateChecks.KernelLC.F24

open CFSG.SectionRank.Native

meta def tgt : Array Nat := Id.run do
  let D := fi24Ext
  let mut ops : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0)]
  let mut regs : Array Nat :=
    (Array.range D.nregs).map fun r => if r == 0 then 0 else if r == 1 then 1 else 2
  let mut out : Array Nat := #[]
  let mulI := fun (ops : Array (Nat × Nat)) (a b : Nat) =>
    match ops.findIdx? (· == (a, b)) with
    | some i => if i ≥ 3 then (ops, i) else (ops.push (a, b), ops.size)
    | none => (ops.push (a, b), ops.size)
  for o in D.prog do
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
  return out

meta def regsAfter : Array Nat := Id.run do
  let D := fi24primeData
  let mut regs : Array Nat :=
    (Array.range D.nregs).map fun r => if r == 0 then 0 else if r == 1 then 1 else 2
  for (o, s) in D.prog.zipIdx do
    match o with
    | .mul _ _ k => regs := regs.set! k tgt[s]!
    | .pow _ _ k => regs := regs.set! k tgt[s]!
  return regs

meta def targetsM : Array (Array Nat) := (tgt.extract 0 fi24primeData.prog.length).map fun t => #[t]

meta def outsM : Array (Array Nat) := fi24primeData.outs.toArray.map fun o => #[regsAfter[o]!]

meta def cubesM : Array (Array Nat) :=
  let b := fi24primeData.prog.length
  (Array.range 4).map fun i => #[tgt[b + 2 * i]!, tgt[b + 2 * i + 1]!]

meta def pairsM : Array (Array Nat) := Id.run do
  let b := fi24primeData.prog.length + 8
  let mut t : Array Nat := Array.replicate 16 0
  let mut s := 0
  for i in [0:4] do
    for j in [0:i] do
      t := t.set! (4 * i + j) tgt[b + s]!
      t := t.set! (4 * j + i) tgt[b + s + 1]!
      s := s + 2
  return t.map fun v => #[v]

end CertificateChecks.KernelLC.F24

#kmisc_packarrs CertificateChecks.KernelLC.F24.TT CertificateChecks.KernelLC.F24.targetsM 20
#kmisc_packarrs CertificateChecks.KernelLC.F24.TO CertificateChecks.KernelLC.F24.outsM 20
#kmisc_packarrs CertificateChecks.KernelLC.F24.TC CertificateChecks.KernelLC.F24.cubesM 20
#kmisc_packarrs CertificateChecks.KernelLC.F24.TP CertificateChecks.KernelLC.F24.pairsM 20

public section

namespace CertificateChecks.KernelLC.F24

open CFSG.KC.LocalComp.Replay CFSG.SectionRank.Native

theorem kReplay : replayOK CFSG.KD.LC.F24.lay CFSG.KD.LC.F24.V CFSG.KD.LC.F24.P TT
    CFSG.KD.LC.F24.N fi24primeData TO (fun _ => 0) = true := by
  quickRfl

end CertificateChecks.KernelLC.F24
