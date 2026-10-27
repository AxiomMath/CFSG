module

public import Certificates.Kernel.LocalComp.L34NGen
public import Certificates.Kernel.LocalComp.L34Gen2
public meta import Certificates.Kernel.LocalComp.L34NGen
public meta import Certificates.Kernel.LocalComp.L34Gen2

public section

namespace CertificateChecks.KernelLC.L34F946Gen

open CFSG.PSL3Four.Native
open CertificateChecks.KernelLC.L34Gen Certificates.L34OuterGen

meta def isO3 (x : Array Nat) : Bool := x != idTab 42 && comp 42 x (comp 42 x x) == idTab 42

meta def cm (x y : Array Nat) : Bool := comp 42 x y == comp 42 y x

meta def inA (e9 : Array (Array Nat)) (x g : Array Nat) : Bool :=
  e9.any fun e => comp 42 x g == comp 42 e x

meta def rowsA : Array (Array Nat) := Id.run do
  let e9 := e9T ()
  let sI := posIn sPts
  let mut out := #[]
  for k in [0:rRun.1.size] do
    let x := rRun.1[k]!
    if isO3 x && inA e9 x a₀T && inA e9 x b₀T then
      match sI[x]? with
      | some s => out := out.push #[k, s, 0]
      | none =>
        let c := (sPts.findIdx? fun c => cm c x && !(inA e9 c a₀T && inA e9 c b₀T)).getD 0
        out := out.push #[k, 0, c]
  return out

meta def bfsW (h0 h1 : Array Nat) : Std.HashMap (Array Nat) (Nat × Nat) := Id.run do
  let mut m : Std.HashMap (Array Nat) (Nat × Nat) := {}
  m := m.insert (idTab 42) (0, 0)
  let mut fr := #[idTab 42]
  for _ in [0:64] do
    if fr.isEmpty then break
    let mut nf := #[]
    for y in fr do
      let (l, wd) := m.getD y (0, 0)
      for k in [0:2] do
        let z := comp 42 y (if k == 0 then h0 else h1)
        if !m.contains z then
          m := m.insert z (l + 1, wd + k * 2 ^ l)
          nf := nf.push z
    fr := nf
  return m

meta def rowZ (k : Nat) (x : Array Nat) : Array Nat := Id.run do
  let z := t3aT
  let tg := #[z, x, comp 42 z x, comp 42 (comp 42 z z) x]
  let mut pools : Array (Array (Nat × Nat)) := #[#[], #[]]
  for j in [1:sPts.size] do
    match (List.range 4).find? (fun t => cm sPts[j]! tg[t]!) with
    | some t => pools := pools.modify (if t == 1 then 0 else 1) (·.push (j, t))
    | none => pure ()
  for (ja, ta) in pools[0]! do
    for (jb, tb) in pools[1]! do
      let m := bfsW sPts[ja]! sPts[jb]!
      if m.size == 20160 then
        let ws := (List.range 3).map fun i => m.getD gensS[i]! (0, 0)
        if ws.all (fun p => p.1 ≤ 32) then
          return #[k, 0, ja, ta, jb, tb] ++ (ws.foldl (fun a p => a ++ #[p.1, p.2]) #[])
  return #[k, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

meta def rowsZ : Array (Array Nat) := Id.run do
  let sI := posIn sPts
  let mut out := #[]
  for k in [0:rRun.1.size] do
    let x := rRun.1[k]!
    if isO3 x && cm x t3aT then
      match sI[x]? with
      | some s => out := out.push #[k, s, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      | none => out := out.push (rowZ k x)
  return out

meta def lK : Array (Array Nat) :=
  let sI := posIn sPts
  #[#[sI.getD a₀T 0, sI.getD b₀T 0, sI.getD t3aT 0]]

end CertificateChecks.KernelLC.L34F946Gen

end
