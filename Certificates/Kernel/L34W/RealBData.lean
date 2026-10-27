module

public import Certificates.Kernel.L34W.OutData

public section

namespace CertificateChecks.KernelL34W

open CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def rbEl (c : ℕ) : MElt := (c / 16, ((c / 4 % 4 : ℕ) : ZMod 4), ((c % 4 : ℕ) : ZMod 4))

@[expose] def rbMasks (κ : ZMod 4 × ZMod 4) : Array Nat :=
  #[(List.range 64).foldl (fun s j =>
      if isBhM κ (rbEl (64 * (j / 16) + j % 16)) then s + 2 ^ j else s) 0,
    (List.range 64).foldl (fun s k => if isAhM κ (k, 0, 0) then s + 2 ^ k else s) 0]

@[expose] def rbHdr : Array (Array Nat) := kGensC.toArray.map rbMasks

@[expose] def rbCell (κ : ZMod 4 × ZMod 4) (Ah : List MElt) (bt : Array MElt) (w : MElt) : Nat :=
  let β := fun x : MElt => bt.getD (encM x) oneM
  if eqKM κ (β w) w then
    let wi := invM w
    let tests : List MElt :=
      ((List.range 64).map fun k => (k, 0, 0)) ++ ((List.range 16).map fun ab => rbEl ab)
    match tests.find? (fun x => !eqKM κ (β (β x)) (mulM (mulM w x) wi)) with
    | some x => 1024 + encM x
    | none =>
      let u := fun v => mulM (mulM v (β v)) w
      match Ah.find? (fun v => eqKM κ (u v) oneM) with
      | some v => 2048 + encM v
      | none =>
        match Ah.find? (fun v => (mulM (u v) (u v)).1 == 0 && !eqKM κ (mulM (u v) (u v)) oneM) with
        | some v => 3072 + encM v
        | none => 4096
  else 0

@[expose] def rbRow (κ : ZMod 4 × ZMod 4) (Bh Ah : List MElt) (i t : ℕ) : Array Nat :=
  if !repInS.contains i && liftsK κ i then
    let g : MElt := (t, 0, 0)
    let gi := invM g
    let bt := (Array.range 1024).map fun c => mulM (mulM g (betaRepM i (rbEl c))) gi
    let β := fun x : MElt => bt.getD (encM x) oneM
    if Bh.all fun x => eqKM κ (β x) x then
      (Array.range 1024).map fun c => rbCell κ Ah bt (rbEl c)
    else #[]
  else #[]

@[expose] def rbArr : Array (Array Nat) :=
  kGensC.toArray.flatMap fun κ =>
    let Bh := allM.filter (isBhM κ)
    let Ah := allM.filter fun x => isAhM κ (x.1, 0, 0)
    (Array.range 2304).map fun r => rbRow κ Bh Ah (r / 64) (r % 64)

end CertificateChecks.KernelL34W

end
