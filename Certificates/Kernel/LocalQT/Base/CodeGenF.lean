module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.LocalQT.Pipe.Twin
public import Certificates.Kernel.LocalQT.Pipe.Twin

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_fz " pre:ident cId:ident tId:ident qpId:ident wId:ident zz:num ww:num : command => do
  let P := pre.getId
  let zi := zz.getNat
  let w := ww.getNat
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qpId
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let C ← liftTermElabM <| unsafe evalConst (Array (List Nat) × Array Nat × Array Nat) cN
  let T ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) tN
  let qp ← liftTermElabM <| unsafe evalConst (List (Nat × Nat)) qN
  let wits ← liftTermElabM <| unsafe evalConst (List (List Nat × List Nat × Nat)) wN
  let G := qp.toArray.map fun p => T[p.1]!
  let g := G.size
  let n := G[0]!.size
  let Ts := C.1
  let par := C.2.1
  let cl := C.2.2
  let gen := fun (i : Nat) => ((List.range g).find? fun j => cl[par[i]! * (2 * g) + j]! == i).getD 0
  let mut path : Array Nat := #[]
  let mut i := zi
  while i != 0 do
    path := path.push (gen i)
    i := par[i]!
  let mut z : Array Nat := Array.range n
  for t in path.reverse do
    z := z.map fun q => G[t]![q]!
  let TS := wits.toArray.map fun wt => pk w Ts[wt.2.2]!.toArray
  withSync do
    addDef (P ++ `ZT) natT (lit (pk w z))
    addTreeT (P ++ `TS) TS

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_bfs " pre:ident cId:ident gg:num ww:num nbb:num wW:num : command => do
  let P := pre.getId
  let g := gg.getNat
  let w := ww.getNat
  let nb := nbb.getNat
  let W := wW.getNat
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let C ← liftTermElabM <| unsafe evalConst (Array (List Nat) × Array Nat × Array Nat) cN
  let codes := C.1.map fun l => pk w l.toArray
  let km := (1 <<< (w * nb)) - 1
  let ord := (Array.range codes.size).qsort fun a b => (codes[a]! &&& km) < (codes[b]! &&& km)
  let mut rank := Array.replicate codes.size 0
  for j in [0:ord.size] do
    rank := rank.set! ord[j]! j
  let cl := (Array.range C.2.2.size).map fun i => if i % (2 * g) < g then C.2.2[i]! else 0
  let rows := fun (a : Array Nat) => (Array.range ((a.size + 63) / 64)).map fun r =>
    pk W ((Array.range 64).map fun j => a.getD (64 * r + j) 0)
  withSync do
    addTreeT (P ++ `BO) rank
    addTreeT (P ++ `IB) ord
    addTreeT (P ++ `PT) (rows C.2.1)
    addTreeT (P ++ `CT) (rows cl)

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_node " pre:ident x:ident tId:ident jj:num ww:num : command => do
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let T ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) tN
  withSync <| addDef (pre.getId ++ x.getId) natT (lit (pk ww.getNat T[jj.getNat]!))

end
