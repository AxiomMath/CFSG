module

public import Certificates.Kernel.L34W.OutData
public import Certificates.Kernel.L34W.RealBW

public section

namespace CertificateChecks.KernelL34W

open CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def rbEl (c : ℕ) : MElt := (c / 16, ((c / 4 % 4 : ℕ) : ZMod 4), ((c % 4 : ℕ) : ZMod 4))

@[expose] def rbMasks (κ : ZMod 4 × ZMod 4) : Array Nat :=
  #[(List.range 64).foldl (fun s j =>
      if isBhM κ (rbEl (64 * (j / 16) + j % 16)) then s + 2 ^ j else s) 0,
    (List.range 64).foldl (fun s k => if isAhM κ (k, 0, 0) then s + 2 ^ k else s) 0]

@[expose] def rbHdr : Array (Array Nat) := kGensC.toArray.map rbMasks

@[expose] def rbKB (κ : ZMod 4 × ZMod 4) : Array Bool :=
  (Array.range 16).map fun c => decide (inKC κ ((c / 4 : ℕ) : ZMod 4) ((c % 4 : ℕ) : ZMod 4))

@[expose] def rbEq (kb : Array Bool) (x y : MElt) : Bool :=
  x.1 == y.1 && kb.getD (4 * (x.2.1 - y.2.1).val + (x.2.2 - y.2.2).val) false

@[expose] def rbTests : List MElt :=
  ((List.range 64).map fun k => (k, 0, 0)) ++ ((List.range 16).map fun ab => rbEl ab)

@[expose] def rbCell (kb : Array Bool) (Ah : List MElt) (bt : Array MElt) (w : MElt) : Nat :=
  let β := fun x : MElt => bt.getD (encM x) oneM
  if rbEq kb (β w) w then
    let u := fun v => mulM (mulM v (β v)) w
    match Ah.find? (fun v => rbEq kb (u v) oneM) with
    | some v => 2048 + encM v
    | none =>
      match Ah.find? (fun v => let u2 := mulM (u v) (u v); u2.1 == 0 && !rbEq kb u2 oneM) with
      | some v => 3072 + encM v
      | none =>
        let wi := invM w
        match rbTests.find? (fun x => !rbEq kb (β (β x)) (mulM (mulM w x) wi)) with
        | some x => 1024 + encM x
        | none => 4096
  else 0

@[expose] def rbRow (kb : Array Bool) (Bh Ah : List MElt) (i t : ℕ) : Array Nat :=
  let g : MElt := (t, 0, 0)
  let gi := invM g
  let β := fun x : MElt => mulM (mulM g (betaRepM i x)) gi
  if Bh.all fun x => rbEq kb (β x) x then
    let bt := (Array.range 1024).map fun c => β (rbEl c)
    (Array.range 1024).map fun c => rbCell kb Ah bt (rbEl c)
  else #[]

@[expose] def rbArrC : Array (Array Nat) :=
  kGensC.toArray.flatMap fun κ =>
    let kb := rbKB κ
    let Bh := allM.filter fun x => zT0.contains x.1 && rbEq kb (mulM x x) oneM
    let ahK := (Array.range 64).map fun k : ℕ =>
      Bh.all fun b => rbEq kb (mulM (k, 0, 0) b) (mulM b (k, 0, 0))
    let Ah := allM.filter fun x => ahK.getD x.1 false
    let rows := (Array.range 36).map fun i => !repInS.contains i && liftsK κ i
    (Array.range 2304).map fun r =>
      if rows.getD (r / 64) false then rbRow kb Bh Ah (r / 64) (r % 64) else #[]

@[expose] def rbHexN (b : ByteArray) (o n : ℕ) : ℕ :=
  (List.range n).foldl (fun s k => 16 * s + hexDigit (b.get! (o + k))) 0

@[expose] def rbArr : Array (Array Nat) := Id.run do
  let b := rbWHex.toUTF8
  let mut out : Array (Array Nat) := Array.replicate 13824 #[]
  for k in [0:b.size / 11] do
    let r := rbHexN b (11 * k) 4
    let c := rbHexN b (11 * k + 4) 3
    let v := rbHexN b (11 * k + 7) 4
    out := out.modify r fun row => (if row.size == 0 then Array.replicate 1024 0 else row).set! c v
  return out

end CertificateChecks.KernelL34W

end
