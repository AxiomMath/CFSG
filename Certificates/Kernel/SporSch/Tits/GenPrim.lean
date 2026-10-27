module

public import Certificates.Kernel.SporSch.Tits.GenStab
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Tits.GenStab
public meta import Lean

open Lean Elab Command

namespace CFSG.KS.GenPrim

open CFSG.KS.RawGen CFSG.KS.GenStab

meta def leaves (F : Name) (n w o k : Nat) : CoreM (Array (Array Nat)) := do
  let mut G : Array (Array Nat) := #[]
  for j in [0:k] do
    G := G.push (unpackN n w (← litOf (F ++ Name.mkSimple s!"L{o + j}")))
  return G

end CFSG.KS.GenPrim

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.GenStab CFSG.KS.GenPrim in
elab "#kst_words " pre:ident nn:num ww:num tId:ident kk:num wId:ident : command => do
  let n := nn.getNat
  let w := ww.getNat
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let T ← liftCoreM <| leaves tN n w 0 kk.getNat
  let W ← liftTermElabM <| unsafe evalConst (List (List Int)) wN
  let vals := W.toArray.map fun wd => pack w (wv n T (T.map (inv n)) wd)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (pre.getId ++ `W) vals

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.GenStab CFSG.KS.GenPrim in
elab "#kst_forest " pre:ident nn:num ww:num gId:ident oo:num kk:num rId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let G ← liftCoreM <| leaves gN n w oo.getNat kk.getNat
  let R ← liftTermElabM <| unsafe evalConst (List Nat) rN
  let m := R.length
  let mut lab := Array.replicate n m
  let mut dep := Array.replicate n 0
  let mut par := Array.replicate n 0
  let mut gl := Array.replicate n 0
  let mut q : Array Nat := #[]
  for c in [0:m] do
    lab := lab.set! R[c]! c
    q := q.push R[c]!
  let mut cs : Array Nat := #[q.size]
  let mut h := 0
  for _ in [0:n] do
    if h < q.size then
      let x := q[h]!
      h := h + 1
      for i in [0:G.size] do
        let y := G[i]![x]!
        if lab[y]! == m then
          lab := lab.set! y lab[x]!
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          gl := gl.set! y i
          q := q.push y
      cs := cs.push q.size
  let N := q.size
  let mut pos := Array.replicate n (N + 1)
  for k in [0:N] do
    pos := pos.set! q[k]! k
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `REP) natT (lit (pack w R.toArray))
    addDef (P ++ `N) natT (lit N)
    addDef (P ++ `Q) natT (lit (pack w q))
    addDef (P ++ `POS) natT (lit (pack w pos))
    addDef (P ++ `C) natT (lit (pack w cs))
    addDef (P ++ `LAB) natT (lit (pack w lab))
    addDef (P ++ `DEP) natT (lit (pack w dep))
    addDef (P ++ `PAR) natT (lit (pack w par))
    addDef (P ++ `GL) natT (lit (pack w gl))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.GenStab CFSG.KS.GenPrim in
elab "#kst_merge " pre:ident nn:num ww:num gId:ident sId:ident k0:num lc:num nl:num rId:ident
    oo:num ss:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let K0 := k0.getNat
  let Lc := lc.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let G ← liftCoreM <| leaves gN n w 0 2
  let s ← liftTermElabM <| unsafe evalConst String sN
  let R ← liftTermElabM <| unsafe evalConst (List Nat) rN
  let b := s.toUTF8
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let hx := fun (o d : Nat) => (List.range d).foldl (fun a t => a * 16 + hv (b.get! (o + t))) 0
  let S := ss.getNat
  let NS := (Lc + S - 1) / S
  let mut tps : Array Nat := #[]
  let mut pps : Array Nat := #[]
  let mut cks : Array Nat := #[]
  for l in [0:nl.getNat] do
    let x := R[oo.getNat + l]!
    let mut lab := Array.ofFn (n := n) fun i => if i.val = x then 0 else i.val
    let mut tp := Array.replicate n Lc
    let mut pp := Array.replicate n 0
    let mut ck : Array Nat := #[]
    for k in [0:Lc] do
      if k % S == 0 then ck := ck.push (pack w lab)
      let o := 7 * (K0 + Lc * l + k)
      let i := hx o 1 % 2
      let u := hx (o + 1) 3 % n
      let v := hx (o + 4) 3 % n
      let lp := lab[G[i]![u]!]!
      let lq := lab[G[i]![v]!]!
      if lq != lp then
        tp := tp.set! lq k
        pp := pp.set! lq lp
        lab := lab.map fun z => if z == lq then lp else z
    while ck.size ≤ NS do
      ck := ck.push (pack w lab)
    cks := cks ++ ck ++ Array.replicate (128 - ck.size) 0
    tps := tps.push (pack 12 tp)
    pps := pps.push (pack w pp)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `TP) tps
    addTree (P ++ `PP) pps
    addTree (P ++ `A) cks
