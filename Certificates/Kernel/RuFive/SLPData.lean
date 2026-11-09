module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Kernel.RuFive.Data
meta import Std.Data.HashMap

namespace CertificateChecks.KernelRuFive.SLPGen

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne CFSG.RankThree.Native

meta def subst (p : Nat × Nat) (sym : Nat) (s : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut j := 0
  while j < s.size do
    if j + 1 < s.size && s[j]! == p.1 && s[j + 1]! == p.2 then
      out := out.push sym
      j := j + 2
    else
      out := out.push s[j]!
      j := j + 1
  return out

meta def best (seqs : Array (Array Nat)) : (Nat × Nat) × Nat := Id.run do
  let mut cnt : Std.HashMap (Nat × Nat) Nat := {}
  for s in seqs do
    for i in [0:s.size - 1] do
      let p := (s[i]!, s[i + 1]!)
      cnt := cnt.insert p (cnt.getD p 0 + 1)
  let mut bp := (0, 0)
  let mut bk := 0
  for (p, k) in cnt.toList do
    if k > bk || (k == bk && (p.1 < bp.1 || (p.1 == bp.1 && p.2 < bp.2))) then
      bp := p
      bk := k
  return (bp, bk)

meta def grammar (nL : Nat) (ws : Array (Array Nat)) : Array (Nat × Nat) × Array Nat := Id.run do
  let mut seqs := ws
  let mut rules : Array (Nat × Nat) := #[]
  for _ in [0:100000] do
    let (p, k) := best seqs
    if k < 2 then break
    let sym := nL + rules.size
    rules := rules.push p
    seqs := seqs.map (subst p sym)
  let mut tops : Array Nat := #[]
  for s in seqs do
    if s.size == 0 then
      tops := tops.push 0
    else
      let mut t := s[s.size - 1]!
      for i in [0:s.size - 1] do
        rules := rules.push (s[s.size - 2 - i]!, t)
        t := nL + rules.size - 1
      tops := tops.push t
  return (rules, tops)

meta partial def runs : List Nat → Array (Array Nat)
  | [] => #[]
  | len :: rest => #[(rest.take len).toArray] ++ runs (rest.drop len)

meta def vals (L : Array (Array Nat)) (rules : Array (Nat × Nat)) : Array (Array Nat) := Id.run do
  let mut vs := L
  for p in rules do
    vs := vs.push (CFSG.KS.RawGen.comp 4060 vs[p.1]! vs[p.2]!)
  return vs.extract L.size vs.size

meta def lets : Array (Array Nat) :=
  (Array.range ruCase0Arrs.size).foldl (fun acc j =>
    (acc.push ruCase0Arrs[j]!).push (invCand 4060 ruCase0Arrs[j]!)) #[]

meta def gR : Array (Nat × Nat) × Array Nat := grammar 16 (runs wordsM)

meta def gaR : Array (Array Nat) := gR.1.map fun p => #[p.1 ||| (p.2 <<< 16)]
meta def taR : Array (Array Nat) := gR.2.map fun t => #[t]
meta def vaR : Array (Array Nat) := vals lets gR.1

end CertificateChecks.KernelRuFive.SLPGen

public section

#kmisc_packarrs CertificateChecks.KernelRuFive.PRG CertificateChecks.KernelRuFive.SLPGen.gaR 32
#kmisc_packarrs CertificateChecks.KernelRuFive.PRT CertificateChecks.KernelRuFive.SLPGen.taR 16
#kmisc_packarrs CertificateChecks.KernelRuFive.PRV CertificateChecks.KernelRuFive.SLPGen.vaR 12

end
