module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.Certificates.Kernel.BfsPinKeySound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.LocalComp.BfsGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.BfsPinSound

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.BfsGen in
elab "#lc_bfs_key " pre:ident gId:ident psId:ident n:num w:num ll:num : command => do
  let P := pre.getId
  let n := n.getNat
  let w := w.getNat
  let L := ll.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let psN ← liftCoreM <| realizeGlobalConstNoOverload psId
  let gs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) gN
  let ps ← liftTermElabM <| unsafe evalConst (List Nat) psN
  let gens := gs.toArray
  let (pts, edges) := search n w gens
  let N := pts.size
  unless L > 0 && N % L == 0 do throwError "#lc_bfs_key: {N} points, slices of {L}"
  let K := N / L
  let tv := pts.map (pack w)
  let ev := edges.map (pack 16)
  let keyOf := fun (a : Array Nat) => ps.foldr (fun p acc => a[p]! + n * acc) 0
  let order := ((Array.range N).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!)
  let counts := (Array.range (K + 1)).map fun s =>
    (edges.extract 0 (L * s)).foldl (fun m r => r.foldl max m) 0 + 1
  let natE := natT
  let c := fun (s : Name) => mkConst (P ++ s)
  let nE := lit n
  let wE := lit w
  let psE := mkConst psN
  let csP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.canonSl)
    #[nE, wE, c `T, lit L, mkBVar 0]))
  let rsP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.runSlB)
    #[nE, wE, c `ng, psE, c `G, c `T, c `E, lit L, c `C, mkBVar 0]))
  let thm := fun (nm : Name) (ty v : Expr) =>
    CFSG.KC.addThmDecl <| { name := P ++ nm, levelParams := [], type := ty, value := v }
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addDef (P ++ `ng) natT (lit gens.size)
    addDef (P ++ `N) natT (lit N)
    addTree (P ++ `T) tv
    addTree (P ++ `E) ev
    addTree (P ++ `K) order
    addTree (P ++ `C) counts
    for s in [0:K] do
      thm (Name.mkSimple s!"cs{s}") (mkApp csP (lit s)).headBeta reflBoolTrue
      thm (Name.mkSimple s!"rs{s}") (mkApp rsP (lit s)).headBeta reflBoolTrue
    let beqPf := fun (a b : Expr) => mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) a b reflBoolTrue
    let hN := beqPf (c `N) (mkApp2 (mkConst ``Nat.mul) (lit L) (lit K))
    let hL := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit 1) (lit L) reflBoolTrue
    let hC0 := beqPf (mkApp (c `C) (lit 0)) (lit 1)
    let hCK := beqPf (mkApp (c `C) (lit K)) (c `N)
    let hc := forallChain csP K fun s => c (Name.mkSimple s!"cs{s}")
    let hr := forallChain rsP K fun s => c (Name.mkSimple s!"rs{s}")
    let runV := mkAppN (mkConst ``CFSG.KC.BfsPin.runFB_of_slices)
      #[nE, wE, c `ng, c `N, lit L, lit K, psE, c `G, c `T, c `E, c `C, hN, hL, hc, hC0, hCK, hr]
    let runT ← Meta.MetaM.run' (Meta.inferType runV)
    thm `run runT runV

end
