module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutHInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CertificateChecks.KernelSpor.AH25

open CFSG.EvenSporadicStandard.TwoFi22.DS81

meta def bM : Array (Array Nat) := autHBasis

meta def ptM (m x : Nat) : Nat :=
  (List.range 10).foldr (fun i acc => if m.testBit i then (bM[i]!)[acc]! else acc) x

meta def witM : Array (Array Nat) := Id.run do
  let mut inv : Array Nat := Array.replicate 3510 2048
  for m in [0:1024] do
    inv := inv.set! (ptM m 0) m
  let mut out : Array Nat := Array.replicate 3510 0
  for q in [0:3510] do
    if inv[q]! < 1024 then
      out := out.set! q inv[q]!
    else
      match (List.range 1023).find? (fun k => ptM (k + 1) q == q) with
      | some k => out := out.set! q (1024 + k + 1)
      | none => out := out.set! q 0
  return #[out]

meta def idM : Array Nat := Array.ofFn (n := 3510) fun i => i.val

meta def phiM (m : Nat) : Array Nat :=
  (List.range 10).foldr (fun i acc => if m.testBit i then CFSG.KS.RawGen.comp 3510 bM[i]! acc
    else acc) idM

meta def bestPair (ws : List (Array Nat)) : Option (Nat × Nat) := Id.run do
  let mut c : Std.HashMap (Nat × Nat) Nat := {}
  for w in ws do
    for i in [0:w.size - 1] do
      let p := (w[i]!, w[i + 1]!)
      c := c.insert p (c.getD p 0 + 1)
  let mut best : Option ((Nat × Nat) × Nat) := none
  for (p, n) in c.toList do
    if n ≥ 2 then
      match best with
      | none => best := some (p, n)
      | some (q, k) =>
        if n > k || (n == k && (p.1 < q.1 || (p.1 == q.1 && p.2 < q.2))) then best := some (p, n)
  return best.map (·.1)

meta def replacePair (w : Array Nat) (a b s : Nat) : Array Nat := Id.run do
  let mut o : Array Nat := #[]
  let mut i := 0
  while i < w.size do
    if i + 1 < w.size && w[i]! == a && w[i + 1]! == b then
      o := o.push s
      i := i + 2
    else
      o := o.push w[i]!
      i := i + 1
  return o

meta partial def repair (ws : List (Array Nat)) (rules : Array (Nat × Nat)) :
    List (Array Nat) × Array (Nat × Nat) :=
  match bestPair ws with
  | none => (ws, rules)
  | some (a, b) => repair (ws.map fun w => replacePair w a b (7 + rules.size)) (rules.push (a, b))

meta def slpM : Array (Nat × Nat) × Array Nat := Id.run do
  let (ws, rules0) := repair [(autHWord 11).toArray, (autHWord 12).toArray] #[]
  let mut rules := rules0
  let mut ends : Array Nat := #[]
  for w in ws do
    let mut acc := w[0]!
    for i in [1:w.size] do
      rules := rules.push (acc, w[i]!)
      acc := 7 + rules.size - 1
    ends := ends.push acc
  return (rules, ends)

meta def regsM : Array (Array Nat) := Id.run do
  let z := autHZ
  let mut R : Array (Array Nat) := #[]
  for j in [0:7] do
    let v := phiM autHMasks[j]!
    R := R.push (CFSG.KS.RawGen.comp 3510 v (CFSG.KS.RawGen.comp 3510 z v))
  for (a, b) in slpM.1 do
    R := R.push (CFSG.KS.RawGen.comp 3510 R[a]! R[b]!)
  return R

meta def tabM : Array (Array Nat) :=
  #[slpM.1.foldl (fun acc p => (acc.push p.1).push p.2) #[], autHMasks.toArray,
    slpM.2.push slpM.1.size]

end CertificateChecks.KernelSpor.AH25

#kmisc_packarrs CertificateChecks.KernelSpor.AH25B CertificateChecks.KernelSpor.AH25.bM 12

#kmisc_packarrs CertificateChecks.KernelSpor.AH25W CertificateChecks.KernelSpor.AH25.witM 11

#kmisc_packarrs CertificateChecks.KernelSpor.AH25R CertificateChecks.KernelSpor.AH25.regsM 12

#kmisc_packarrs CertificateChecks.KernelSpor.AH25T CertificateChecks.KernelSpor.AH25.tabM 10

end
