module

public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

public section

namespace CertificateChecks.KernelSlpRel

open CFSG.KC.Eval

public meta def fiMul3Interp (d A B : Nat) : Nat := Id.run do
  let N := d * d
  let LO := (1 <<< N) - 1
  let RM := (1 <<< d) - 1
  let CI := (List.range d).foldl (fun acc i => acc ||| (1 <<< (d * i))) 0
  let A1 := A &&& LO
  let A2 := A >>> N
  let B1 := B &&& LO
  let B2 := B >>> N
  let mut x1 := 0
  let mut x2 := 0
  for k in [0:d] do
    let a1 := (A1 >>> k) &&& CI
    let a2 := (A2 >>> k) &&& CI
    let b1 := (B1 >>> (d * k)) &&& RM
    let b2 := (B2 >>> (d * k)) &&& RM
    let q := a1 * b1 + a2 * b2
    let m := a1 * b2 + a2 * b1
    let t := (x1 ||| m) ^^^ (x2 ||| q)
    let z1 := (x2 ||| m) ^^^ t
    let z2 := (x1 ||| q) ^^^ t
    x1 := z1
    x2 := z2
  return x1 + (x2 <<< N)

public meta def fiSufMul3 (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.nat d) := args[0]? | throw "fiSufMul3: no dimension"
  let mut ms : Array Nat := #[]
  for a in args.extract 1 args.size do
    match a with
    | .nat v => ms := ms.push v
    | _ => throw "fiSufMul3: a matrix is not a number"
  let some last := ms.back? | throw "fiSufMul3: no matrix"
  let mut acc := last
  for i in (List.range (ms.size - 1)).reverse do
    acc := fiMul3Interp d ms[i]! acc
  return #[(.anonymous, .nat acc)]

end CertificateChecks.KernelSlpRel

end
