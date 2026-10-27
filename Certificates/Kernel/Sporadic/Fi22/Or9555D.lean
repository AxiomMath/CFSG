module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
public import CFSG.Assembly.Defs

public section

namespace CertificateChecks.KernelSpor.Or9555

open CFSG.AGLEmbedding.KFactProofs.Fi22Five

meta def gen : Array Nat × Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let starts : Array (Array Nat × Nat) :=
    #[(s0Arr, 1), (st1Arr, 1575), (st2Arr, 22400), (st3Arr, 37800)]
  let mut recs : Array Nat := #[]
  let mut keys : Array Nat := #[]
  let mut rootCuts : Array (Array Nat × Nat × Nat) := #[]
  let mut cuts : Array (Array Nat × Nat × Nat) := #[]
  for (st, size) in starts do
    let (sets, par, lab) := orbSearchA orbGens st size
    let m := sets.size
    let mut ch : Array (Array Nat) := Array.replicate m #[m, m]
    for v in [1:m] do
      ch := ch.modify par[v]! fun c => c.set! lab[v]! v
    let mut order : Array Nat := #[]
    let mut stack : Array Nat := #[0]
    for _ in [0:2 * m + 2] do
      if h : stack.size > 0 then
        let v := stack.back!
        stack := stack.pop
        order := order.push v
        let c := ch[v]!
        if (c)[1]! < m then stack := stack.push (c)[1]!
        if (c)[0]! < m then stack := stack.push (c)[0]!
    let mut resid : Array Nat := Array.replicate m 0
    let mut isCut : Array Bool := Array.replicate m false
    for t in [0:m] do
      let v := order[m - 1 - t]!
      let c := ch[v]!
      let r := 1 + (if (c)[0]! < m then resid[(c)[0]!]! else 0) +
        (if (c)[1]! < m then resid[(c)[1]!]! else 0)
      if v == 0 || r ≥ 1000 then
        isCut := isCut.set! v true
        resid := resid.set! v 0
      else
        resid := resid.set! v r
    let base := recs.size
    let mut posOf : Array Nat := Array.replicate m 0
    for t in [0:m] do
      posOf := posOf.set! order[t]! (base + t)
    let mut endOf : Array Nat := Array.replicate m 0
    for t in [0:m] do
      let v := order[m - 1 - t]!
      let c := ch[v]!
      let e := if (c)[1]! < m then endOf[(c)[1]!]! else if (c)[0]! < m then endOf[(c)[0]!]!
        else posOf[v]! + 1
      endOf := endOf.set! v e
    for t in [0:m] do
      let v := order[t]!
      let c := ch[v]!
      let fl := (if (c)[0]! < m then 1 else 0) + (if (c)[1]! < m then 2 else 0)
      let k := hashA sets[v]!
      recs := recs.push (k * 65536 + fl)
      keys := keys.push k
      if isCut[v]! then
        if v == 0 then rootCuts := rootCuts.push (sets[v]!, posOf[v]!, endOf[v]!)
        else cuts := cuts.push (sets[v]!, posOf[v]!, endOf[v]!)
  let all := rootCuts ++ cuts
  for c in [0:all.size] do
    let (_, p, _) := all[c]!
    recs := recs.set! p (recs[p]! + 4 + 8 * c)
  let order := (Array.range keys.size).qsort fun a b => keys[a]! < keys[b]!
  return (recs, all.map (·.1), all.map fun (_, p, e) => p + e * 1048576, order)

meta def blocks (a : Array Nat) : Array (Array Nat) :=
  (Array.range ((a.size + 255) / 256)).map fun b => a.extract (256 * b) (256 * b + 256)

meta def recsM : Array (Array Nat) := blocks gen.1
meta def cutSetsM : Array (Array Nat) := gen.2.1
meta def cutPosM : Array (Array Nat) := gen.2.2.1.map fun x => #[x]
meta def orderM : Array (Array Nat) := blocks gen.2.2.2
meta def hashM : Array (Array Nat) := #[hashTab]

end CertificateChecks.KernelSpor.Or9555

end

set_option Elab.async false

#kmisc_packarrs CertificateChecks.KernelSpor.Or9555T CertificateChecks.KernelSpor.Or9555.recsM 80
#kmisc_packarrs CertificateChecks.KernelSpor.Or9555C CertificateChecks.KernelSpor.Or9555.cutSetsM 12
#kmisc_packarrs CertificateChecks.KernelSpor.Or9555P CertificateChecks.KernelSpor.Or9555.cutPosM 64
#kmisc_packarrs CertificateChecks.KernelSpor.Or9555K CertificateChecks.KernelSpor.Or9555.orderM 16
#kmisc_packarrs CertificateChecks.KernelSpor.Or9555R CertificateChecks.KernelSpor.Or9555.hashM 64
