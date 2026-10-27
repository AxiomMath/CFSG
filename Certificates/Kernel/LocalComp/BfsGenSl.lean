module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.Certificates.Kernel.BfsPinSliceSound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.LocalComp.BfsGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.BfsGen in
elab "#lc_bfs_sl " pre:ident gId:ident n:num w:num ll:num : command => do
  let P := pre.getId
  let n := n.getNat
  let w := w.getNat
  let L := ll.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let gs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) gN
  let gens := gs.toArray
  let (pts, edges) := search n w gens
  let N := pts.size
  unless L > 0 && N % L == 0 do throwError "#lc_bfs_sl: {N} points, slices of {L}"
  let K := N / L
  let tv := pts.map (pack w)
  let ev := edges.map (pack 16)
  let order := ((Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!)
  let counts := (Array.range (K + 1)).map fun s =>
    (edges.extract 0 (L * s)).foldl (fun m r => r.foldl max m) 0 + 1
  let natE := natT
  let c := fun (s : Name) => mkConst (P ++ s)
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mkApp2 (mkConst ``Nat.mul) nE wE
  let csP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.canonSl)
    #[nE, wE, c `T, lit L, mkBVar 0]))
  let rsP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.runSl)
    #[nE, wE, c `ng, c `G, c `T, c `E, lit L, c `C, mkBVar 0]))
  let thm := fun (nm : Name) (ty v : Expr) =>
    CFSG.KC.addThmDecl <| { name := P ++ nm, levelParams := [], type := ty, value := v }
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addDef (P ++ `ng) natT (lit gens.size)
    addDef (P ++ `N) natT (lit N)
    addTree (P ++ `T) tv
    addTree (P ++ `E) ev
    addTree (P ++ `S) order
    addTree (P ++ `C) counts
    for s in [0:K] do
      thm (Name.mkSimple s!"cs{s}") (mkApp csP (lit s)).headBeta reflBoolTrue
      thm (Name.mkSimple s!"rs{s}") (mkApp rsP (lit s)).headBeta reflBoolTrue
    let hszT := isTrue (mkApp2 (mkConst ``CFSG.KS.Raw.szOK) nE wE)
    thm `hsz hszT reflBoolTrue
    let canG := mkLambda `k .default natE (mkAppN (mkConst ``CFSG.KS.Prim.canonK)
      #[nE, wE, mE, nwE, mkApp (c `G) (mkBVar 0)])
    let hGT := isTrue (mkApp2 (mkConst ``CFSG.KC.Enum.allN) (c `ng) canG)
    thm `hG hGT reflBoolTrue
    let h0T := isTrue (mkApp2 (mkConst ``Nat.beq) (mkApp (c `T) (lit 0))
      (mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE))
    thm `h0 h0T reflBoolTrue
    let hDT := isTrue (mkApp3 (mkConst ``CFSG.KC.BfsPin.distinctK) (c `N) (c `T) (c `S))
    thm `hD hDT reflBoolTrue
    let eqN := fun (a b : Expr) => mkApp3 (mkConst ``Eq [1]) natE a b
    let beqPf := fun (a b : Expr) => mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) a b reflBoolTrue
    let hN := mkApp2 (mkConst ``Eq.refl [1]) natE (c `N)
    let hL := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit 1) (lit L) reflBoolTrue
    let hC0 := beqPf (mkApp (c `C) (lit 0)) (lit 1)
    let hCK := beqPf (mkApp (c `C) (lit K)) (c `N)
    let hc := forallChain csP K fun s => c (Name.mkSimple s!"cs{s}")
    let hr := forallChain rsP K fun s => c (Name.mkSimple s!"rs{s}")
    let okT := isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.bfsK)
      #[nE, wE, c `ng, c `G, c `N, c `T, c `E, c `S])
    let okV := mkAppN (mkConst ``CFSG.KC.BfsPin.bfsK_of_slices)
      #[nE, wE, c `ng, c `N, lit L, lit K, c `G, c `T, c `E, c `S, c `C, hN, hL, c `hsz, c `hG,
        hc, c `h0, c `hD, hC0, hCK, hr]
    let _ := eqN
    thm `ok okT okV

end
