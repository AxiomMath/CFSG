module

public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.LocalComp.BfsGenSl
public meta import Certificates.Kernel.B3S3.Gen
public meta import Certificates.Kernel.LocalComp.BfsGen
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.BfsGen CFSG.KC.B3S3Gen in
elab "#kenum_sl " pre:ident gId:ident bId:ident nn:num ww:num ll:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let L := ll.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let (pts, edges) := search n w gens
  let N := pts.size
  unless L > 0 && N % L == 0 do throwError "#kenum_sl: {N} points, slices of {L}"
  let K := N / L
  let tv := pts.map (pack w)
  let ev := edges.map (pack 16)
  let order := (Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!
  let keyOf := fun (a : Array Nat) => base.toList.foldr (fun p acc => a[p]! + n * acc) 0
  let kv := pts.map keyOf
  let korder := ((Array.range kv.size).qsort fun a b => kv[a]! < kv[b]!).toList
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
    addDef (P ++ `L) natT (lit L)
    addDef (P ++ `K) natT (lit K)
    addTree (P ++ `T) tv
    addTree (P ++ `E) ev
    addTree (P ++ `S) order
    addTree (P ++ `C) counts
    addDef (P ++ `SK) listT (listE korder)
    for s in [0:K] do
      thm (Name.mkSimple s!"cs{s}") (mkApp csP (lit s)).headBeta reflBoolTrue
      thm (Name.mkSimple s!"rs{s}") (mkApp rsP (lit s)).headBeta reflBoolTrue
    thm `hsz (isTrue (mkApp2 (mkConst ``CFSG.KS.Raw.szOK) nE wE)) reflBoolTrue
    let canG := mkLambda `k .default natE (mkAppN (mkConst ``CFSG.KS.Prim.canonK)
      #[nE, wE, mE, nwE, mkApp (c `G) (mkBVar 0)])
    thm `hG (isTrue (mkApp2 (mkConst ``CFSG.KC.Enum.allN) (c `ng) canG)) reflBoolTrue
    thm `h0 (isTrue (mkApp2 (mkConst ``Nat.beq) (mkApp (c `T) (lit 0))
      (mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE))) reflBoolTrue
    thm `hD (isTrue (mkApp3 (mkConst ``CFSG.KC.BfsPin.distinctK) (c `N) (c `T) (c `S)))
      reflBoolTrue
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
    thm `ok okT okV
    let psE := mkApp2 (mkConst ``Array.toList [0]) natT (mkConst bN)
    let keysT := isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.keysSK)
      #[nE, wE, psE, c `N, c `T, c `SK])
    thm `keys keysT reflBoolTrue

end
