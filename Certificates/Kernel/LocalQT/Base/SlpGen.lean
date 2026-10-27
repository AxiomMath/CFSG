module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.LocalQT.Pipe.Twin
public import Certificates.Kernel.LocalQT.Pipe.Twin

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_slp " pre:ident tId:ident ww:num qpId:ident rs:num : command => do
  let P := pre.getId
  let w := ww.getNat
  let RS := rs.getNat
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qpId
  let T ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) tN
  let qp ← liftTermElabM <| unsafe evalConst (List (Nat × Nat)) qN
  let codes := T.map (pk w)
  let mask := (1 <<< (64 * w)) - 1
  let rows := (qp.toArray.map fun p => (Array.range RS).map fun k =>
    (codes[p.1]! >>> (64 * w * k)) &&& mask).flatten
  withSync do
    addTreeT (P ++ `TF) codes
    addTreeT (P ++ `RT) rows

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_set " pre:ident cId:ident tId:ident qpId:ident ww:num nbb:num : command => do
  let P := pre.getId
  let w := ww.getNat
  let nb := nbb.getNat
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qpId
  let C ← liftTermElabM <| unsafe evalConst (Array (List Nat) × Array Nat × Array Nat) cN
  let T ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) tN
  let qp ← liftTermElabM <| unsafe evalConst (List (Nat × Nat)) qN
  let G := qp.toArray.map fun p => T[p.1]!
  let Ts := C.1
  let par := C.2.1
  let codes := Ts.map fun l => pk w l.toArray
  let km := (1 <<< (w * nb)) - 1
  let ord := (Array.range Ts.size).qsort fun a b => (codes[a]! &&& km) < (codes[b]! &&& km)
  let mut rank := Array.replicate Ts.size 0
  for j in [0:ord.size] do
    rank := rank.set! ord[j]! j
  let mut dep := Array.replicate Ts.size 0
  let mut gen := Array.replicate Ts.size 0
  for i in [1:Ts.size] do
    let p := par[i]!
    dep := dep.set! i (dep[p]! + 1)
    let mut t := 0
    for k in [0:G.size] do
      if Ts[p]!.map (fun x => G[k]![x]!) == Ts[i]! then
        t := k
        break
    gen := gen.set! i t
  let E := ord.map fun i => codes[i]!
  let PG := ord.map fun i => rank[par[i]!]! + (gen[i]! <<< 15) + (dep[i]! <<< 18)
  withSync do
    addTreeT (P ++ `E) E
    addTreeT (P ++ `PG) PG

end
