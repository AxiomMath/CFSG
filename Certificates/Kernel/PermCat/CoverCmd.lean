module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.PermutationCatalogueJson
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command
open CFSG.KC.Tab CFSG.KS.RawGen
open CFSG.Certificates.PermutationCatalogue.Data CFSG.Certificates.PermutationCatalogue.Json

namespace CFSG.KC.PermCatCmd

meta def bitsFor (n : Nat) : Nat := Id.run do
  let mut d := 1
  while (1 <<< d) < n do
    d := d + 1
  return d

meta def natListE (l : Array Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

meta def leafVal (env : Environment) (F : Name) (k : Nat) : Option Nat :=
  match env.find? (F ++ Name.mkSimple s!"L{k}") with
  | some ci => match ci.value? (allowOpaque := true) with
    | some (.lit (.natVal v)) => some v
    | _ => none
  | none => none

meta def dispatch (ty : Expr) (leaf : Nat → Expr) (cnt : Nat) : Expr :=
  let h := Nat.log2 (2 * max cnt 1 - 1)
  let motive := mkLambda `_ .default (mkConst ``Bool) ty
  let rec go (lo size : Nat) (fuel : Nat) : Expr :=
    match fuel with
    | 0 => leaf (min lo (cnt - 1))
    | fuel + 1 =>
      if size ≤ 1 then leaf (min lo (cnt - 1))
      else
        let half := size / 2
        mkAppN (mkConst ``Bool.rec [Level.one])
          #[motive, go lo half fuel, go (lo + half) half fuel,
            mkApp2 (mkConst ``Nat.ble) (lit (lo + half)) (mkBVar 0)]
  mkLambda `i .default natT (go 0 (1 <<< h) (h + 1))

meta def bfs (n : Nat) (gs : Array (Array Nat)) : Array (Array Nat) × Array (Array Nat) := Id.run do
  let root := Array.range n
  let mut pts : Array (Array Nat) := #[root]
  let mut idx : Std.HashMap (Array Nat) Nat := ({} : Std.HashMap (Array Nat) Nat).insert root 0
  let mut edges : Array (Array Nat) := #[]
  let mut i := 0
  while i < pts.size do
    let mut row := #[]
    for g in gs do
      let t := pts[i]!
      let y := Array.ofFn (n := n) fun x => g[t[x.val]!]!
      match idx.get? y with
      | some j => row := row.push j
      | none =>
        idx := idx.insert y pts.size
        row := row.push pts.size
        pts := pts.push y
    edges := edges.push row
    i := i + 1
  return (pts, edges)

meta def keyOf (w : Nat) (B : Array Nat) (t : Array Nat) : Nat := Id.run do
  let mut k := 0
  for i in [0:B.size] do
    k := k ||| (t[B[i]!]! <<< (w * i))
  return k

meta def rowBlocks (w top : Nat) (B : Array Nat) (amb : Array (Array Nat)) (row : Row)
    (el : Array (Array Nat)) (posEl : Nat → Nat) : Array (Nat × Nat × Nat) := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array (Nat × Nat × Nat) := #[]
  for h in [0:amb.size] do
    if seen.contains (keyOf w B amb[h]!) then continue
    let cv := row.cover[h]!
    let r := amb[(row.transitions[cv.transition]!).representative]!
    let a := posEl cv.left
    let p := el[a]!
    let mut mn := top
    for k in el do
      let mut key := 0
      for i in [0:B.size] do
        key := key ||| (p[r[k[B[i]!]!]!]! <<< (w * i))
      seen := seen.insert key
      mn := min mn key
    out := out.push (mn, a, cv.transition)
  return out.qsort (fun x y => x.1 < y.1)

meta def sortInv (v : Array Nat) : Array Nat × Array Nat := Id.run do
  let order := (Array.range v.size).qsort fun a b => v[a]! < v[b]!
  let mut inv := Array.replicate order.size 0
  for k in [0:order.size] do
    inv := inv.set! order[k]! k
  return (order, inv)

meta def compT (t u : Array Nat) : Array Nat := u.map (t[·]!)

meta def actKey (w m : Nat) (x : Array Nat) (k : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | nb + 1, o => (x[(k >>> o) &&& m]! <<< o) ||| actKey w m x k nb (o + w)

meta def shortWords (w cap : Nat) (B : Array Nat) (xs : Array (Array Nat))
    (tg : Array (Array Nat)) : Array (Option (Array Nat)) := Id.run do
  let nb := B.size
  let m := (1 <<< w) - 1
  let keyT : Array Nat → Nat := fun t => Id.run do
    let mut k := 0
    for i in [0:nb] do
      k := k ||| (t[B[i]!]! <<< (w * i))
    return k
  let tk := tg.map keyT
  let k0 := Id.run do
    let mut k := 0
    for i in [0:nb] do
      k := k ||| (B[i]! <<< (w * i))
    return k
  let mut par : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert k0 0
  let mut queue : Array Nat := #[k0]
  let mut qi := 0
  let mut left := (tk.filter (· != k0)).size
  while qi < queue.size && left > 0 && queue.size < cap do
    let s := queue[qi]!
    qi := qi + 1
    for l in [0:xs.size] do
      let k' := actKey w m xs[l]! s nb 0
      unless par.contains k' do
        par := par.insert k' (s * 8 + l)
        queue := queue.push k'
        if tk.contains k' then left := left - (tk.filter (· == k')).size
  return tk.map fun k => Id.run do
    unless par.contains k do return none
    let mut word := #[]
    let mut c := k
    while c != k0 do
      let v := par[c]!
      word := word.push (v % 8)
      c := v / 8
    return some word

end CFSG.KC.PermCatCmd

open CFSG.KC.PermCatCmd in
elab "#kpermcat_cat " pre:ident path:str size:num hash:num nn:num ww:num rows:num amb:num
    gens:num bot:num tpId:ident cnt:num per:num ew:num bs:num* : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let B := bs.map (·.getNat)
  let top := 1 <<< (w * B.size)
  let b ← readPinned path.getString size.getNat hash.getNat
  let wd : Nat → Nat := fun i =>
    if 2 * i + 1 < b.size then b[2 * i]!.toNat + (b[2 * i + 1]!.toNat <<< 8) else 0
  let Pd := parse wd (b.size / 2) n rows.getNat amb.getNat gens.getNat bot.getNat
  unless Pd.ok do throwError "#kpermcat_cat: the parser rejected {path.getString}"
  let I := Pd.input
  let nRows := I.rows.size
  let env ← getEnv
  let TP ← liftCoreM <| realizeGlobalConstNoOverload tpId
  let em := (1 <<< ew.getNat) - 1
  let mut posOf : Std.HashMap Nat Nat := {}
  let mut ptsP : Array Nat := #[]
  for k in [0:(cnt.getNat + per.getNat - 1) / per.getNat] do
    let some v := leafVal env TP k | throwError "#kpermcat_cat: no literal leaf {k} of {TP}"
    for e in [0:per.getNat] do
      if per.getNat * k + e < cnt.getNat then
        let x := (v >>> (ew.getNat * e)) &&& em
        posOf := posOf.insert x (per.getNat * k + e)
        ptsP := ptsP.push x
  let amT := I.ambient.tabs
  let ambP := amT.map (pack w)
  let N := amT.size
  let pos : Nat → CommandElabM Nat := fun x => do
    let some q := posOf[x]? | throwError "#kpermcat_cat: a permutation is not in {TP}"
    return q
  let mut els : Array (Array (Array Nat)) := #[]
  let mut posKs : Array (Std.HashMap Nat Nat) := #[]
  let mut NG : Array Nat := #[]
  let mut NK : Array Nat := #[]
  let mut NR : Array Nat := #[]
  let mut EW : Array Nat := #[]
  let mut WA : Array Nat := #[]
  let mut WJ : Array Nat := #[]
  for i in [0:nRows] do
    let row := I.rows[i]!
    let R := P ++ Name.mkSimple s!"R{i}"
    let gs := row.gens.map (amT[·]!)
    let (el, edges) := bfs n gs
    unless el.size == row.elems.tabs.size do
      throwError "#kpermcat_cat: row {i}: {el.size} elements generated, {row.elems.tabs.size} listed"
    let KL := el.map (pack w)
    let mut posK : Std.HashMap Nat Nat := {}
    for k in [0:KL.size] do
      posK := posK.insert KL[k]! k
    let mut posEl : Array Nat := #[]
    for t in row.elems.tabs do
      let some q := posK[pack w t]? | throwError "#kpermcat_cat: row {i}: a listed element is not generated"
      posEl := posEl.push q
    let mut GP : Array Nat := #[]
    for g in row.gens do
      GP := GP.push (← pos ambP[g]!)
    let mut RI : Array Nat := #[]
    for t in row.transitions do
      RI := RI.push (← pos ambP[t.representative]!)
    let bl := rowBlocks w top B amT row el (posEl[·]!)
    let wa := bitsFor KL.size
    let wj := bitsFor RI.size
    let BL := bl.map fun (mk, a, j) => a ||| (j <<< wa) ||| (mk <<< (wa + wj))
    let e := bitsFor KL.size
    let (order, inv) := sortInv KL
    els := els.push el
    posKs := posKs.push posK
    NG := NG.push gs.size
    NK := NK.push KL.size
    NR := NR.push RI.size
    EW := EW.push e
    WA := WA.push wa
    WJ := WJ.push wj
    liftCoreM <| withOptions (Elab.async.set · false) do
      addDef (R ++ `KL) (mkApp (mkConst ``List [0]) natT) (natListE KL)
      addTree (R ++ `KT) KL
      addTree (R ++ `G) (gs.map (pack w))
      addTree (R ++ `GP) GP
      addTree (R ++ `E) (edges.map (pack e))
      addTree (R ++ `C) #[1, KL.size]
      addTree (R ++ `S) order
      addTree (R ++ `SI) inv
      addTree (R ++ `RI) RI
      addDef (R ++ `BL) (mkApp (mkConst ``List [0]) natT) (natListE BL)
  let mut TS : Array Nat := #[]
  let mut TRP : Array Nat := #[]
  let mut TCP : Array Nat := #[]
  let mut TCIP : Array Nat := #[]
  let mut TT : Array Nat := #[]
  let mut TF : Array Nat := #[]
  let mut TW : Array Nat := #[]
  let mut WD : Array Nat := #[]
  let mut TOff : Array Nat := #[]
  for i in [0:nRows] do
    TOff := TOff.push TS.size
    let row := I.rows[i]!
    let gs := row.gens.map (amT[·]!)
    for t in row.transitions do
      let c := amT[t.conjugator]!
      let ci := I.ambientInv[t.conjugator]!
      let r := amT[t.representative]!
      let posT := posKs[t.target]!
      let mut fw := 0
      let xs := gs.push r
      for k in [0:xs.size] do
        let y := compT ci (compT xs[k]! c)
        let some q := posT[pack w y]?
          | throwError "#kpermcat_cat: row {i}: a forward conjugate is not in row {t.target}"
        fw := fw ||| (q <<< (15 * k))
      TS := TS.push i
      TRP := TRP.push (← pos ambP[t.representative]!)
      TCP := TCP.push (← pos ambP[t.conjugator]!)
      TCIP := TCIP.push (← pos (pack w ci))
      TT := TT.push t.target
      TF := TF.push fw
      TW := TW.push WD.size
      let tg := (I.rows[t.target]!).gens.map fun g => compT c (compT amT[g]! ci)
      let ws := shortWords w 256 B (#[r] ++ gs) tg
      for k in [0:ws.size] do
        let wo : Array Nat := match ws[k]! with
          | some wo => wo
          | none => (t.words[k]!).map fun
            | none => 0
            | some j => j + 1
        let mut W := 0
        for l in [0:wo.size] do
          W := W ||| (wo[l]! <<< (3 * l))
        WD := WD.push (wo.size ||| (W <<< 16))
  TOff := TOff.push TS.size
  let (SK, SKI) := sortInv (ptsP.map fun x => Id.run do
    let mut k := 0
    for j in [0:B.size] do
      k := k ||| (((x >>> (w * B[j]!)) &&& ((1 <<< w) - 1)) <<< (w * j))
    return k)
  let listT := mkApp (mkConst ``List [0]) natT
  let fnT2 := mkForall `j .default natT natT
  let rowName := fun (i : Nat) (s : Name) => P ++ Name.mkSimple s!"R{i}" ++ s
  liftCoreM <| withOptions (Elab.async.set · false) do
    for s in [`KL, `BL] do
      addDef (P ++ s.appendAfter "s") (mkForall `i .default natT listT)
        (dispatch listT (fun i => mkConst (rowName i s)) nRows)
    for s in [`KT, `G, `GP, `E, `C, `S, `SI, `RI] do
      addDef (P ++ s.appendAfter "s") (mkForall `i .default natT fnT2)
        (dispatch fnT2 (fun i => mkConst (rowName i s)) nRows)
    for (s, v) in [(`NG, NG), (`NK, NK), (`NR, NR), (`EW, EW), (`WA, WA), (`WJ, WJ), (`TS, TS),
        (`TRP, TRP), (`TCP, TCP), (`TCIP, TCIP), (`TT, TT), (`TF, TF), (`TW, TW), (`WD, WD),
        (`TOff, TOff), (`SK, SK), (`SKI, SKI)] do
      addTree (P ++ s) v
