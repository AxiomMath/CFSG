module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.SMod20CollCheck

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.SmithE CFSG.Fischer.Native CFSG.Sporadic.Th.Native

public meta def nStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "nStep: expected no arguments"
  let S2 := collS2
  let pack := fun (w : Nat) (l : List Nat) => l.foldr (fun x acc => x + 2 ^ w * acc) 0
  let lineMask := fun (a b : Nat) => (List.range 21).foldl (fun m z =>
    if collP S2 z a b then m ||| (1 <<< z) else m) 0
  let mut lines : Array Nat := #[]
  let mut li : Array Nat := Array.replicate 441 0
  for a in [0:21] do
    for b in [0:21] do
      if a != b then
        let m := lineMask a b
        match lines.findIdx? (· == m) with
        | some i => li := li.set! (21 * a + b) i
        | none =>
          li := li.set! (21 * a + b) lines.size
          lines := lines.push m
      else
        li := li.set! (21 * a + b) (21 + a)
  if lines.size != 21 then throw s!"nStep: {lines.size} lines"
  let lm := lines.toList ++ (List.range 21).map (1 <<< ·)
  let low := fun (m : Nat) => ((List.range 21).find? fun z => m.testBit z).getD 0
  let lmA := lm.toArray
  let mp := (List.range 1764).map fun t => low (lmA[t / 42]! &&& lmA[t % 42]!)
  let I := collInvs S2 (collMeet S2)
  let R := (List.range 21).map fun y0 =>
    (I.toList.filter fun s => s[0]! == y0).map fun s => pack 5 s.toList
  let nat1 := fun (l : List Nat) => Val.list (l.toArray.map .nat)
  return #[(`CL, nat1 uaCo.toList), (`CP, .nat (pack 9 uaCo.toList)),
    (`LI, .nat (pack 6 li.toList)), (`LM, .nat (pack 21 lm)), (`MP, .nat (pack 5 mp)),
    (`R, .list (R.toArray.map nat1))]

end CertificateChecks.KernelSmithEK
