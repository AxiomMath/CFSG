module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.SporSch.GenStabBT
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Certificates.Kernel.SporSch.HeadSplitSound
public import Certificates.Kernel.SporSch.GenStabBT

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchBT CFSG.KS.RawGenSplit in
elab "#kss_rebase " pre:ident nn:num ww:num lch:num aId:ident bId:ident ord:num sd:num em:num :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let LCH := lch.getNat
  let order := ord.getNat
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let B ← liftTermElabM <| unsafe evalConst (List Nat) bN
  let kO := A.size
  let ident := Array.range n
  let mut S : Array (Array Nat) := A
  let mut W : Array (List Int) := A.map fun _ => []
  let mut base : Array Nat := B.toArray
  let levelsOf := fun (S : Array (Array Nat)) (base : Array Nat) => Id.run do
    let mut out : Array (Std.HashMap Nat (Array Nat × List Int)) := #[]
    for i in [0:base.size] do
      let idx := (List.range S.size).filter fun j =>
        (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
      let steps : Array (Array Nat × Int) :=
        (idx.map fun (j : Nat) => (S[j]!, ((j + 1 : Nat) : Int))).toArray ++
        (idx.map fun (j : Nat) => (inv n S[j]!, -(((j + 1 : Nat) : Int)))).toArray
      let b := base[i]!
      let mut tr : Std.HashMap Nat (Array Nat × List Int) := (∅ : Std.HashMap Nat _).insert b (ident, [])
      let mut q : Array Nat := #[b]
      let mut h := 0
      while h < q.size do
        let x := q[h]!
        let (tx, wx) := tr.get! x
        for (s, l) in steps do
          let y := s[x]!
          if !tr.contains y then
            tr := tr.insert y (comp n s tx, l :: wx)
            q := q.push y
        h := h + 1
      out := out.push tr
    return out
  let mut lv := levelsOf S base
  let sizeOf := fun (lv : Array (Std.HashMap Nat (Array Nat × List Int))) =>
    lv.foldl (fun acc t => acc * t.size) 1
  let mut st := sd.getNat
  let mut guard := 0
  while sizeOf lv < order && guard < 10000 do
    guard := guard + 1
    let mut r := ident
    let mut rw : List Int := []
    for _ in [0:40] do
      st := (st * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      let j := (st >>> 33) % kO
      r := comp n A[j]! r
      rw := ((j + 1 : Nat) : Int) :: rw
    let mut g := r
    let mut gw := rw
    let mut lvl := base.size
    for i in [0:base.size] do
      let y := g[base[i]!]!
      match lv[i]!.get? y with
      | some (t, tw) =>
        g := comp n (inv n t) g
        gw := (tw.reverse.map fun z => -z) ++ gw
      | none =>
        if lvl == base.size then lvl := i
    if lvl == base.size && g != ident then
      let moved := (List.range n).find? fun x => g[x]! != x
      base := base.push moved.get!
    if g != ident then
      S := S.push g
      W := W.push gw
      lv := levelsOf S base
  if sizeOf lv != order then
    throwError "the Schreier–Sims run reached order {sizeOf lv}, not {order}"
  if em.getNat == 0 then
    let wl := (W.extract kO S.size).map List.length
    logInfo m!"strong {S.size}, base {base}, orbits {lv.map (·.size)}, words: total {wl.foldl (· + ·) 0}, max {wl.foldl max 0}, lengths {wl}"
    return
  let lT := mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) (mkConst ``Int))
  if em.getNat == 4 then
    let (recs, _, _, _) := levels n w S base false
    let c : Ctx := { P, n, w, kS := S.size, nb := base.size }
    withSync do
      addDef (P ++ `pn) natT (lit n)
      addDef (P ++ `pw) natT (lit w)
      addDef (P ++ `pkS) natT (lit S.size)
      addDef (P ++ `pnb) natT (lit base.size)
      addDef (P ++ `pkO) natT (lit kO)
      addDef (P ++ `D) lT (wordsE (W.extract kO S.size))
      addDef (P ++ `pLCH) natT (lit LCH)
      addDef (P ++ `NL) natT (lit ((n + LCH - 1) / LCH))
      addTree (P ++ `S) (S.map (pack w))
      addTree (P ++ `SI) ((S.map (inv n)).map (pack w))
      addTree (P ++ `LR) recs
      addDef (P ++ `BP) natT (lit (pack w base))
      for i in [0:c.nb] do
        addRefl (P ++ Name.mkSimple s!"lh{i}") (orbHdT c (lit i))
    return
  let (recs, cnts, trs, tris) := levels n w S base true
  let c : Ctx := { P, n, w, kS := S.size, nb := base.size }
  withSync do
    addDef (P ++ `pn) natT (lit n)
    addDef (P ++ `pw) natT (lit w)
    addDef (P ++ `pkS) natT (lit S.size)
    addDef (P ++ `pnb) natT (lit base.size)
    addDef (P ++ `pkO) natT (lit kO)
    addDef (P ++ `D) lT (wordsE (W.extract kO S.size))
    addDef (P ++ `pLCH) natT (lit LCH)
    addDef (P ++ `pCH) natT (lit 0)
    addDef (P ++ `NL) natT (lit ((n + LCH - 1) / LCH))
    addDef (P ++ `NS) natT (lit 0)
    for i in [0:base.size] do
      addDef (P ++ Name.mkSimple s!"NS{i}") natT (lit 0)
    for i in [0:base.size] do
      addDef (P ++ Name.mkSimple s!"cnt{i}") natT (lit cnts[i]!)
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) ((S.map (inv n)).map (pack w))
    addTree (P ++ `LR) recs
    addTree (P ++ `TR) trs
    addTree (P ++ `TRI) tris
    addDef (P ++ `BP) natT (lit (pack w base))
    if 2 ≤ em.getNat then
      addHead c kO (P ++ `D)
    if 3 ≤ em.getNat then
      for i in [0:c.nb] do
        addRefl (P ++ Name.mkSimple s!"lh{i}") (lvHdT c (lit i))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#kss_head_sl " pre:ident lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let kO ← natOf (P ++ `pkO)
  withSync do
    for j in [lo.getNat:min hi.getNat c.kS] do
      addRefl (P ++ Name.mkSimple s!"hd{j}") (isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.headJ)
        #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, lit kO, c.k `D, lit c.nb, c.k `BP,
          lit j]))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#kss_head_join " pre:ident : command => do
  let P := pre.getId
  let c ← ctxOf P
  let kO ← natOf (P ++ `pkO)
  let hjT := fun (jE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.headJ)
    #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, lit kO, c.k `D, lit c.nb, c.k `BP, jE])
  withSync do
    addRefl (P ++ `hrest) (isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.headRest)
      #[c.nE, c.wE, c.mE, lit c.kS, lit kO, c.k `D, lit c.nb, c.k `BP]))
    let lam := mkLambda `j .default natT (hjT (mkBVar 0))
    let hjV := forallChain lam c.kS fun j => mkConst (P ++ Name.mkSimple s!"hd{j}")
    let headT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.headK)
      #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, lit c.kS, lit kO, c.k `D, lit c.nb,
        c.k `BP])
    let v := mkAppN (mkConst ``CFSG.KS.SporSch.headK_of_parts)
      #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, lit c.kS, lit kO, c.k `D, lit c.nb,
        c.k `BP, mkConst (P ++ `hrest), hjV]
    CFSG.KC.addThmDecl <| { name := P ++ `head, levelParams := [], type := headT, value := v }
