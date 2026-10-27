module

public meta import Lean
public meta import Certificates.Kernel.SporSch.Ly.GenLy
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Sporadic.Schreier.LyCheckSylow
public import Certificates.Kernel.SporSch.GenSetReplay
public import Certificates.Kernel.SporSch.Ly.GenLy

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.LySylGen

open CFSG.KC.Tab

meta def natListE (l : List Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc) (mkApp (mkConst ``List.nil [0]) natT)

meta def natListsE (ls : List (List Nat)) : Expr :=
  let lt := mkApp (mkConst ``List [0]) natT
  ls.foldr (fun l acc => mkApp3 (mkConst ``List.cons [0]) lt (natListE l) acc) (mkApp (mkConst ``List.nil [0]) lt)

meta def maskLst (l : List Nat) : Nat := l.foldl (fun acc x => acc ||| (1 <<< x)) 0

end CFSG.KS.SporSch.LySylGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen CFSG.KS.SporSch.LySylGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_syl " pre:ident : command => do
  let P := pre.getId
  let b4 := powM 5 111 (matB ()) 4
  let cs := cStarArr b4
  let us := sylowGens cs
  let (_, par, lab, lam) := sylowBFS us 256
  let n := 256
  let T := mulTabOf n par lab lam
  let pl := (Array.range n).map fun j => par[j]! ||| (lab[j]! <<< 9)
  let rows := (Array.range n).map fun i => (List.range n).foldl (fun acc j => acc ||| ((T[i]!)[j]! <<< (8 * j))) 0
  let iv := (List.range n).foldl (fun acc i => acc ||| (tinv T n i <<< (8 * i))) 0
  let mut cms : Array Nat := #[]
  let mut mask := 0
  let mut sts : Array Nat := #[0]
  for q in [0:n * n] do
    let a := q / n
    let b := q % n
    let c := tcomm T n a b
    if (mask >>> c) % 2 == 0 then
      cms := cms.push (c ||| (a <<< 8) ||| (b <<< 16))
      mask := mask ||| (1 <<< c)
    if (q + 1) % 4096 == 0 then
      sts := sts.push (cms.size + (mask <<< 16))
  let (D, dPar, dA, dB) := derivedTree T n
  let dt := (Array.range D.size).map fun k =>
    D[k]! ||| (dPar[k]! <<< 8) ||| (dA[k]! <<< 16) ||| (dB[k]! <<< 24)
  let ea := fun (L : List (List Nat)) => Id.run do
    let L' := nextEA T n L
    let ms := L'.toArray.map maskLst
    let mut found : Std.HashMap Nat Unit := ∅
    let mut cts : Array Nat := #[0]
    for E in L do
      for x in [0:n] do
        if extendsBy T E x then
          found := found.insert (maskLst (spanBy T E x)) ()
      cts := cts.push found.size
    return (L', ms, cts)
  let (L1, m1, c1) := ea [[0]]
  let (L2, m2, c2) := ea L1
  let (L3, m3, c3) := ea L2
  let (L4, m4, c4) := ea L3
  let ints := mkApp (mkConst ``List [0]) (mkConst ``Int)
  let pairT := mkApp2 (mkConst ``Prod [0, 0]) natT ints
  let clE := invConjugators.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) pairT
      (mkApp4 (mkConst ``Prod.mk [0, 0]) natT ints (lit e.1) (intListE e.2)) acc)
    (mkApp (mkConst ``List.nil [0]) pairT)
  let llT := mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) natT)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `PL) pl
    addTree (P ++ `MT) rows
    addDef (P ++ `IV) natT (lit iv)
    addTree (P ++ `CM) cms
    addDef (P ++ `nC) natT (lit cms.size)
    addTree (P ++ `ST) sts
    addTree (P ++ `DT) dt
    addDef (P ++ `nD) natT (lit dt.size)
    for (s, L, ms, cts) in [("1", L1, m1, c1), ("2", L2, m2, c2), ("3", L3, m3, c3), ("4", L4, m4, c4)] do
      addDef (P ++ Name.mkSimple s!"L{s}") llT (natListsE L)
      addTree (P ++ Name.mkSimple s!"NM{s}") ms
      addTree (P ++ Name.mkSimple s!"CT{s}") cts
      addDef (P ++ Name.mkSimple s!"nN{s}") natT (lit L.length)
    addDef (P ++ `CL) (mkApp (mkConst ``List [0]) pairT) clE

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kly_chain " pre:ident nmI:ident qId:ident ng:num rr:num : command => do
  let P := pre.getId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  let nm := nmI.getId.toString
  liftCoreM <| withOptions (Elab.async.set · false) do
    addChain2 P nm (nm ++ "All") ng.getNat rr.getNat fun q => isTrue (mkApp (mkConst qN) q)

end
