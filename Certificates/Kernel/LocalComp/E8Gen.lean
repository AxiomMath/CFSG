module

public import Certificates.Data.Kernel.WeylE8.Coord
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylDefs
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylDefs
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public meta import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KLC.E8Gen

meta def keyOf (v : List Int) : Nat := Id.run do
  let mut k := 0
  for i in [0:v.length] do
    k := k + ((v[i]! + 2).toNat <<< (4 * i))
  return k

end CFSG.KLC.E8Gen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KLC.E8Gen in
elab "#lc_e8 " pre:ident : command => do
  let P := pre.getId
  let roots ← liftTermElabM <| unsafe evalConst (List (List Int))
    ``CFSG.EvenSmallLie.OmegaEight.Weyl.rootList
  let ra := roots.toArray
  let keys := ra.map keyOf
  let idx : Std.HashMap Nat Nat := (List.range ra.size).foldl (fun m i => m.insert keys[i]! i) {}
  let order := ((List.range ra.size).toArray.qsort fun a b => keys[a]! < keys[b]!)
  let dot := fun (u v : List Int) => (List.zipWith (· * ·) u v).foldl (· + ·) 0
  let refl := fun (r i : Nat) =>
    let x := ra[i]!
    let rv := ra[r]!
    let t := dot x rv / 4
    idx.getD (keyOf (List.zipWith (fun a b => a - t * b) x rv)) 255
  let rts := (List.range 240).toArray.map fun r => pack 8 ((List.range 240).toArray.map (refl r))
  let negs := pack 8 ((List.range 240).toArray.map fun i => idx.getD (keyOf (ra[i]!.map (- ·))) 255)
  let flip := fun (m : Nat) (v : List Int) =>
    (List.range v.length).map fun k => if (m >>> k) % 2 == 1 then -v[k]! else v[k]!
  let sts := (List.range 256).toArray.map fun m =>
    if (List.range 8).foldl (fun a k => a + (m >>> k) % 2) 0 % 2 == 0 then
      pack 8 ((List.range 240).toArray.map fun i => idx.getD (keyOf (flip m ra[i]!)) 255)
    else 0
  let pairs := (List.range 8).flatMap fun a => ((List.range 8).filter (a < ·)).map fun b => (a, b)
  let swapV := fun (a b : Nat) (v : List Int) =>
    (List.range v.length).map fun k => if k == a then v[b]! else if k == b then v[a]! else v[k]!
  let pts := pairs.toArray.map fun (a, b) =>
    pack 8 ((List.range 240).toArray.map fun i => idx.getD (keyOf (swapV a b ra[i]!)) 255)
  let dp := pack 8 (pairs.toArray.map fun (a, b) => 8 * a + b)
  let frameV := fun (k : Nat) => (List.range 8).map fun c : Nat =>
    if c == 2 * (k / 2) then (2 : Int) else if c == 2 * (k / 2) + 1 then (if k % 2 == 0 then -2 else 2)
    else 0
  let fr := (List.range 8).toArray.map fun k => idx.getD (keyOf (frameV k)) 255
  let reflV := fun (r x : List Int) => List.zipWith (fun a b => a - dot x r / 4 * b) x r
  let fts := (List.range 256).toArray.map fun a =>
    pack 8 ((List.range 240).toArray.map fun i =>
      idx.getD (keyOf ((List.range 8).foldl (fun x k =>
        if (a >>> k) % 2 == 1 then reflV (frameV k) x else x) ra[i]!)) 255)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `PT) pts
    addDef (P ++ `DP) natT (lit dp)
    addTree (P ++ `RK) keys
    addTree (P ++ `RT) rts
    addDef (P ++ `SO) natT (lit (pack 8 order))
    addDef (P ++ `NEG) natT (lit negs)
    let c := fun (s : Name) => mkConst (P ++ s)
    let bindT := isTrue (mkAppN (mkConst ``CFSG.KLC.E8.bindRoots)
      #[c `RK, mkConst ``CFSG.EvenSmallLie.OmegaEight.Weyl.rootList])
    CFSG.KC.addThmDecl <| { name := P ++ `bind, levelParams := [], type := bindT, value := reflBoolTrue }
    let sortT := isTrue (mkAppN (mkConst ``CFSG.KLC.E8.sortedOK) #[c `RK, c `SO])
    CFSG.KC.addThmDecl <| { name := P ++ `sorted, levelParams := [], type := sortT, value := reflBoolTrue }
    let rtT := fun (rE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KLC.E8.reflRowOK)
      #[c `RK, rE, mkApp (c `RT) rE])
    for r in [0:240] do
      let nm := P ++ Name.mkSimple s!"rt{r}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := rtT (lit r), value := reflBoolTrue }
    let rtP := mkLambda `r .default natT (rtT (mkBVar 0))
    let hrtV := forallChain rtP 240 fun r => mkConst (P ++ Name.mkSimple s!"rt{r}")
    let hrtT := mkForall `r .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit 240]) (rtT (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `hrt, levelParams := [], type := hrtT, value := hrtV }
    let negT := isTrue (mkAppN (mkConst ``CFSG.KLC.E8.negTabOK) #[c `RK, c `NEG])
    CFSG.KC.addThmDecl <| { name := P ++ `neg, levelParams := [], type := negT, value := reflBoolTrue }
    addTree (P ++ `ST) sts
    let stT := fun (mE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KLC.E8.signRowOK)
      #[c `RK, mE, mkApp (c `ST) mE])
    for m in [0:256] do
      let nm := P ++ Name.mkSimple s!"st{m}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := stT (lit m), value := reflBoolTrue }
    let stP := mkLambda `m .default natT (stT (mkBVar 0))
    let hstV := forallChain stP 256 fun m => mkConst (P ++ Name.mkSimple s!"st{m}")
    let hstT := mkForall `m .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit 256]) (stT (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `hst, levelParams := [], type := hstT, value := hstV }
    addDef (P ++ `FR) natT (lit (pack 8 fr))
    addTree (P ++ `FT) fts
    let frT := isTrue (mkAppN (mkConst ``CFSG.KLC.E8.frameRootsOK) #[c `RK, c `FR])
    CFSG.KC.addThmDecl <| { name := P ++ `froots, levelParams := [], type := frT, value := reflBoolTrue }
    let ftT := fun (aE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KLC.E8.frameRowOK)
      #[c `RK, c `FR, aE, mkApp (c `FT) aE])
    for a in [0, 1, 2, 4, 8, 16, 32, 64, 128] do
      let nm := P ++ Name.mkSimple s!"ft{a}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ftT (lit a), value := reflBoolTrue }
    let one := fun (kE : Expr) => mkAppN (mkConst ``Nat.shiftLeft) #[lit 1, kE]
    let ftP := mkLambda `k .default natT (ftT (one (mkBVar 0)))
    let hftV := forallChain ftP 8 fun k => mkConst (P ++ Name.mkSimple s!"ft{2 ^ k}")
    let hftT := mkForall `k .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit 8]) (ftT (one (mkBVar 1))))
    CFSG.KC.addThmDecl <| { name := P ++ `hft, levelParams := [], type := hftT, value := hftV }

end
