module

public import Certificates.Data.Kernel.SporSch.J4STok
public import Certificates.Data.Kernel.SporSch.J4SCols
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.Gen

meta def toksOf (s : String) : Array Int := Id.run do
  let mut out : Array Int := #[]
  let mut cur : Nat := 0
  let mut neg := false
  let mut inTok := false
  for ch in s.toList do
    let c := ch.toNat
    if 48 ≤ c && c ≤ 57 then
      cur := cur * 10 + (c - 48)
      inTok := true
    else if c == 45 then
      neg := true
    else
      if inTok then
        out := out.push (if neg then -(cur : Int) else (cur : Int))
      cur := 0
      neg := false
      inTok := false
  if inTok then
    out := out.push (if neg then -(cur : Int) else (cur : Int))
  return out

meta def intE (z : Int) : Expr :=
  match z with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

end CFSG.KS.SporSch.Gen

open CFSG.KC.Tab CFSG.KS.SporSch.Gen in
elab "#kss_tokens " pre:ident sId:ident : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let ts := toksOf s
  let intT := mkConst ``Int
  let lst := ts.foldr (fun z acc => mkApp3 (mkConst ``List.cons [0]) intT (intE z) acc)
    (mkApp (mkConst ``List.nil [0]) intT)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `toks) (mkApp (mkConst ``List [0]) intT) lst
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``CFSG.KS.SporSch.tokK) (mkConst (P ++ `chars)) (mkConst (P ++ `toks)))
      (mkConst ``Bool.true)
    CFSG.KC.addThmDecl <| { name := P ++ `tok, levelParams := [], type := ty, value := reflBoolTrue }

open CFSG.KC.Tab CFSG.KS.SporSch.Gen in
elab "#kss_words " pre:ident sId:ident kN:num : command => do
  let P := pre.getId
  let k := kN.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let ts := toksOf s
  let intT := mkConst ``Int
  let lT := mkApp (mkConst ``List [0]) intT
  let mut pos := 0
  let mut ws : Array (Array Int) := #[]
  for _ in [0:k] do
    let len := (ts[pos]!).toNat
    ws := ws.push ((Array.range len).map fun j => ts[pos + 1 + j]!)
    pos := pos + 1 + len
  let ws' := ws
  liftCoreM <| withOptions (Elab.async.set · false) do
    for i in [0:ws'.size] do
      let lst := ws'[i]!.foldr (fun z acc => mkApp3 (mkConst ``List.cons [0]) intT (intE z) acc)
        (mkApp (mkConst ``List.nil [0]) intT)
      addDef (P ++ Name.mkSimple s!"w{i}") lT lst
    let all := (List.range ws'.size).foldr (fun i acc => mkApp3 (mkConst ``List.cons [0]) lT
      (mkConst (P ++ Name.mkSimple s!"w{i}")) acc) (mkApp (mkConst ``List.nil [0]) lT)
    addDef (P ++ `ws) (mkApp (mkConst ``List [0]) lT) all
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``CFSG.KS.SporSch.C11.tokWordsK) (mkConst (P ++ `toks)) (mkConst (P ++ `ws)))
      (mkConst ``Bool.true)
    CFSG.KC.addThmDecl <| { name := P ++ `wtok, levelParams := [], type := ty, value := reflBoolTrue }

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_table " pre:ident aId:ident wN:num mN:num : command => do
  let P := pre.getId
  let w := wN.getNat
  let m := mN.getNat
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let vs := A.map (pack w)
  let natArr := mkApp (mkConst ``Array [0]) natT
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree P vs
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.KS.SporSch.C11.bind2K)
        #[lit w, lit m, mkApp2 (mkConst ``Array.toList [0]) natArr (mkConst aN), mkConst P,
          lit A.size]) (mkConst ``Bool.true)
    CFSG.KC.addThmDecl <| { name := P ++ `bind, levelParams := [], type := ty, value := reflBoolTrue }

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_tree " pre:ident aId:ident wN:num : command => do
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId (A.map (pack wN.getNat))

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_slices " pre:ident fId:ident kN:num sN:num : command => do
  let P := pre.getId
  let k := kN.getNat
  let S := sN.getNat
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let bT := mkConst ``Bool
  let ty := fun (sE : Expr) => mkApp3 (mkConst ``Eq [1]) bT
    (mkApp3 (mkConst ``CFSG.KC.Enum.allBlk) (mkApp2 (mkConst ``Nat.mul) (lit k) sE) (mkConst fN)
      (lit k)) (mkConst ``Bool.true)
  liftCoreM <| withOptions (Elab.async.set · false) do
    for i in [0:S] do
      let nm := P ++ Name.mkSimple s!"s{i}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty (lit i), value := reflBoolTrue }
    let Pl := mkLambda `s .default natT (ty (mkBVar 0))
    let v := forallChain Pl S fun i => mkConst (P ++ Name.mkSimple s!"s{i}")
    let allT := mkForall `s .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit S]) (ty (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := allT, value := v }

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_rows " pre:ident xId:ident : command => do
  let xN ← liftCoreM <| realizeGlobalConstNoOverload xId
  let X ← liftTermElabM <| unsafe evalConst (Array Nat) xN
  let P := (List.range X.size).foldl (fun acc i => acc ||| (X[i]! <<< (128 * i))) 0
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef pre.getId natT (lit P)

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_pairs " pre:ident rId:ident : command => do
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let R ← liftTermElabM <| unsafe evalConst (Array (Array Nat × Array Nat)) rN
  let pk := fun (X : Array Nat) => (List.range X.size).foldl (fun acc i => acc ||| (X[i]! <<< (128 * i))) 0
  let vs := (R.map fun p => pk p.1).toList ++ (R.map fun p => pk p.2).toList
  let lst := vs.foldr (fun v acc => mkApp3 (mkConst ``List.cons [0]) natT (lit v) acc)
    (mkApp (mkConst ``List.nil [0]) natT)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef pre.getId (mkApp (mkConst ``List [0]) natT) lst

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_vec " pre:ident aId:ident : command => do
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let a ← liftTermElabM <| unsafe evalConst (Array Nat) aN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId a

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_sort " pre:ident aId:ident wN:num : command => do
  let P := pre.getId
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let vs := A.map (pack wN.getNat)
  let so := (Array.range A.size).qsort fun i j => vs[i]! < vs[j]!
  let mut soi := Array.replicate A.size 0
  for i in [0:so.size] do
    soi := soi.set! so[i]! i
  let soi' := soi
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `SO) so
    addTree (P ++ `SOI) soi'

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_orbit " pre:ident bId:ident : command => do
  let P := pre.getId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let B ← liftTermElabM <| unsafe evalConst (Array Nat × Array Nat × Array Nat) bN
  let n := B.1.size
  let mut pos := Array.replicate 2048 n
  for i in [0:n] do
    if B.1[i]! < 2048 then pos := pos.set! B.1[i]! i
  let pos' := pos
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `PT) B.1
    addTree (P ++ `PAR) B.2.1
    addTree (P ++ `LAB) B.2.2
    addTree (P ++ `POS) pos'

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_array " pre:ident aId:ident wN:num mN:num : command => do
  let P := pre.getId
  let w := wN.getNat
  let m := mN.getNat
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let a ← liftTermElabM <| unsafe evalConst (Array Nat) aN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef P natT (lit (pack w a))
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.KS.SporSch.C11.bindWK)
        #[lit w, lit m, mkApp2 (mkConst ``Array.toList [0]) natT (mkConst aN), mkConst P])
      (mkConst ``Bool.true)
    CFSG.KC.addThmDecl <| { name := P ++ `bind, levelParams := [], type := ty, value := reflBoolTrue }

end
