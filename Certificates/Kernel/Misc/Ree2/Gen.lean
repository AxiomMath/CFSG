module

public import CFSG.Certificates.Kernel.Misc.Ree2Sound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.Kernel.Misc.Ree2
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

namespace CFSG.KC.Misc.Ree2Gen

open CFSG.Walter.Ree.Bombieri

meta def mpP (x : Nat) : Nat := x &&& 65535
meta def mpN (x : Nat) : Nat := x >>> 16
meta def mpOf (p n : Nat) : Nat := p ||| (n <<< 16)
meta def addMP (x y : Nat) : Nat :=
  let t := (mpP x ||| mpN y) ^^^ (mpN x ||| mpP y)
  mpOf ((mpN x ||| mpN y) ^^^ t) ((mpP x ||| mpP y) ^^^ t)
meta def negMP (x : Nat) : Nat := mpOf (mpN x) (mpP x)
meta def mulXMP (m F x : Nat) : Nat :=
  let y := mpOf (mpP x <<< 1) (mpN x <<< 1)
  if (mpP y >>> m) &&& 1 == 1 then addMP y (negMP F)
  else if (mpN y >>> m) &&& 1 == 1 then addMP y F else y
meta def mulByG (m F g dg x : Nat) : Nat := Id.run do
  let mut acc := 0
  for t in [0:dg + 1] do
    let j := dg - t
    acc := mulXMP m F acc
    if (mpP g >>> j) &&& 1 == 1 then acc := addMP acc x
    else if (mpN g >>> j) &&& 1 == 1 then acc := addMP acc (negMP x)
  return acc

meta def ofCodeMP (c : Nat) : Nat := Id.run do
  let mut p := 0
  let mut n := 0
  let mut c := c
  for i in [0:20] do
    if c % 3 == 1 then p := p ||| (1 <<< i)
    if c % 3 == 2 then n := n ||| (1 <<< i)
    c := c / 3
  return mpOf p n

structure LF where
  m : Nat
  q1 : Nat
  hf : Nat
  F : Nat
  g : Nat
  dg : Nat
  ET : Array Nat
  LG : Array Nat
  ZT : Array Nat

meta def LF.idx (L : LF) (x : Nat) : Nat := mpP x + (mpN x <<< L.m)

meta def mkLF (m F g : Nat) : Except String LF := do
  let q1 := 3 ^ m - 1
  let dg := (mpP g ||| mpN g).log2
  let mut et : Array Nat := Array.mkEmpty q1
  let mut x := 1
  for _ in [0:q1] do
    et := et.push x
    x := mulByG m F g dg x
  if x != 1 then throw "g^q1 ≠ 1"
  let mut lg : Array Nat := Array.replicate (4 ^ m) q1
  for e in [0:q1] do
    let v := et[e]!
    let i := mpP v + (mpN v <<< m)
    if lg[i]! != q1 then throw "g is not primitive"
    lg := lg.set! i e
  let L0 : LF := ⟨m, q1, q1 / 2, F, g, dg, et, lg, #[]⟩
  let zt := (Array.range q1).map fun d => L0.LG[L0.idx (addMP 1 et[d]!)]!
  return { L0 with ZT := zt }

meta def LF.mul (L : LF) (a b : Nat) : Nat := if a == L.q1 || b == L.q1 then L.q1 else (a + b) % L.q1
meta def LF.add (L : LF) (a b : Nat) : Nat :=
  if a == L.q1 then b else if b == L.q1 then a else
  let z := L.ZT[(b + L.q1 - a) % L.q1]!
  if z == L.q1 then L.q1 else (a + z) % L.q1
meta def LF.neg (L : LF) (a : Nat) : Nat := if a == L.q1 then L.q1 else (a + L.hf) % L.q1
meta def LF.sub (L : LF) (a b : Nat) : Nat := L.add a (L.neg b)
meta def LF.inv (L : LF) (a : Nat) : Nat := (L.q1 - a) % L.q1
meta def LF.pw (L : LF) (a n : Nat) : Nat :=
  if n == 0 then 0 else if a == L.q1 then L.q1 else (a * n) % L.q1
meta def LF.res (L : LF) (v : Nat) : Nat := if v % 3 == 0 then L.q1 else if v % 3 == 1 then 0 else L.hf
meta def LF.const (L : LF) (c : Int) : Nat :=
  match c with
  | .ofNat n => L.res n
  | .negSucc n => L.res (2 * (n + 1))

meta def LF.eval (L : LF) (ρ α : Nat → Nat) : PE → Nat
  | .var i => ρ i
  | .atom k => α k
  | .const c => L.const c
  | .add a b => L.add (L.eval ρ α a) (L.eval ρ α b)
  | .sub a b => L.sub (L.eval ρ α a) (L.eval ρ α b)
  | .mul a b => L.mul (L.eval ρ α a) (L.eval ρ α b)
  | .pow a n => L.pw (L.eval ρ α a) n
  | .neg a => L.neg (L.eval ρ α a)

meta def shapeCode (i j : Nat) : Nat := (CFSG.KC.Misc.Ree2.shapeL >>> (5 * (12 * i + j))) &&& 31

meta def LF.det (L : LF) (z0 z1 z2 z3 y : Nat) : Option Nat := Id.run do
  let vars := fun (i : Nat) => if i == 0 then z0 else if i == 1 then z1 else if i == 2 then z2
    else if i == 3 then z3 else if i == 4 then y else L.q1
  let atoms := CFSG.KC.Misc.Ree2.atomL.toArray.map (L.eval vars fun _ => L.q1)
  let cs := CFSG.KC.Misc.Ree2.coefL.toArray.map (L.eval vars fun k => atoms[k]!)
  let mut M : Array Nat := Array.replicate 144 L.q1
  for i in [0:12] do
    for j in [0:12] do
      let s := shapeCode i j
      if s != 0 then M := M.set! (12 * i + j) cs[s - 1]!
  for k in [0:12] do
    let ip := L.inv M[13 * k]!
    for i in [k + 1:12] do
      let l := M[12 * i + k]!
      if l != L.q1 then
        let lp := L.mul l ip
        for j in [k + 1:12] do
          let akj := M[12 * k + j]!
          if akj != L.q1 then
            M := M.set! (12 * i + j) (L.sub M[12 * i + j]! (L.mul lp akj))
  let mut d := 0
  for k in [0:12] do
    if M[13 * k]! == L.q1 then return none
    d := L.mul d M[13 * k]!
  return some d

meta def LF.trim (L : LF) (p : Array Nat) : Array Nat := Id.run do
  let mut p := p
  while p.size > 0 && p.back! == L.q1 do p := p.pop
  return p

meta def LF.padd (L : LF) (a b : Array Nat) : Array Nat :=
  (Array.range (max a.size b.size)).map fun i => L.add (a.getD i L.q1) (b.getD i L.q1)

meta def LF.pmul (L : LF) (a b : Array Nat) : Array Nat := Id.run do
  if a.size == 0 || b.size == 0 then return #[]
  let mut r := Array.replicate (a.size + b.size - 1) L.q1
  for i in [0:a.size] do
    if a[i]! != L.q1 then
      for j in [0:b.size] do
        if b[j]! != L.q1 then r := r.set! (i + j) (L.add r[i + j]! (L.mul a[i]! b[j]!))
  return r

meta def LF.pdivmod (L : LF) (a b : Array Nat) : Array Nat × Array Nat := Id.run do
  let b := L.trim b
  let mut a := L.trim a
  let mut q := Array.replicate (max 1 (a.size + 1 - b.size)) L.q1
  let li := L.inv b.back!
  for _ in [0:a.size + 1] do
    if a.size < b.size || a.size == 0 then break
    let c := L.mul a.back! li
    let sh := a.size - b.size
    q := q.set! sh (L.add q[sh]! c)
    let sub := (Array.replicate sh L.q1) ++ b.map fun x => L.neg (L.mul c x)
    a := L.trim (L.padd a sub)
  return (L.trim q, a)

meta def LF.pxgcd (L : LF) (a b : Array Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let mut r0 := L.trim a
  let mut r1 := L.trim b
  let mut s0 : Array Nat := #[0]
  let mut s1 : Array Nat := #[]
  let mut t0 : Array Nat := #[]
  let mut t1 : Array Nat := #[0]
  for _ in [0:a.size + b.size + 2] do
    if r1.size == 0 then break
    let (q, r) := L.pdivmod r0 r1
    (r0, r1) := (r1, r)
    (s0, s1) := (s1, L.trim (L.padd s0 ((L.pmul q s1).map L.neg)))
    (t0, t1) := (t1, L.trim (L.padd t0 ((L.pmul q t1).map L.neg)))
  return (r0, s0, t0)

meta def LF.interp (L : LF) (xs ys : Array Nat) : Array Nat := Id.run do
  let n := xs.size
  let mut c := ys
  for j in [1:n] do
    for t in [0:n - j] do
      let i := n - 1 - t
      let num := L.sub c[i]! c[i - 1]!
      let den := L.sub xs[i]! xs[i - j]!
      c := c.set! i (L.mul num (L.inv den))
  let mut p : Array Nat := #[]
  for t in [0:n] do
    let i := n - 1 - t
    let mut q := Array.replicate (p.size + 1) L.q1
    for a in [0:p.size] do
      q := q.set! (a + 1) (L.add q[a + 1]! p[a]!)
      q := q.set! a (L.sub q[a]! (L.mul xs[i]! p[a]!))
    q := q.set! 0 (L.add q[0]! c[i]!)
    p := q
  return p

meta def LF.horner (L : LF) (p : Array Nat) (x : Nat) : Nat :=
  p.foldr (fun a acc => L.add a (L.mul x acc)) L.q1

meta def isTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def natListE (l : Array Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkRawNatLit x) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))

meta def addThm (n : Name) (ty v : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name := n, levelParams := [], type := ty, value := v }

meta def addDefE (n : Name) (ty v : Expr) : CoreM Unit :=
  CFSG.KC.Tab.addDef n ty v

meta def packW (w : Nat) (vs : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:vs.size] do
    acc := acc ||| (vs[i]! <<< (w * i))
  return acc

meta def rep32 (L v : Nat) : Nat := Id.run do
  let mut x := 0
  for i in [0:L] do
    x := x ||| (v <<< (32 * i))
  return x

meta def lanes (m x : Nat) : Nat := Id.run do
  let mut L := 0
  for i in [0:m + 1] do
    L := L ||| ((((mpP x) >>> i &&& 1) + 2 * ((mpN x) >>> i &&& 1)) <<< (32 * i))
  return L

meta def assemble (pre : Array Expr) (app zero : Name) (chunks : Array (Nat × Nat × Name)) :
    Expr := Id.run do
  let mut acc := mkAppN (mkConst zero) (pre.push (mkRawNatLit 0))
  let mut done := 0
  for (s, len, thm) in chunks do
    let _ := s
    acc := mkAppN (mkConst app) (pre ++ #[mkRawNatLit done, mkRawNatLit 0, mkRawNatLit len, acc,
      mkConst thm])
    done := done + len
  return acc

meta def chunks (n ch : Nat) : Array (Nat × Nat) :=
  (Array.range ((n + ch - 1) / ch)).map fun i => (i * ch, min ch (n - i * ch))

meta def lit (n : Nat) : Expr := mkRawNatLit n

meta def readNat (n : Name) : CoreM Nat := do
  let some (.defnInfo d) := (← getEnv).find? n | throwError "unknown definition {n}"
  let .lit (.natVal v) := d.value | throwError "{n} is not a literal"
  return v

end CFSG.KC.Misc.Ree2Gen

open CFSG.KC.Misc.Ree2Gen in
elab "#ree2_field " pre:ident mm:num fpN:num fnN:num gcN:num : command => do
  let P := pre.getId
  let m := mm.getNat
  let L ← match mkLF m (mpOf fpN.getNat fnN.getNat) (ofCodeMP gcN.getNat) with
    | .ok L => pure L
    | .error e => throwError e
  let q1 := L.q1
  let nat := mkConst ``Nat
  let c := fun (s : Name) => mkConst (P ++ s)
  let Fl := lanes m L.F
  let ML := (1 <<< (32 * m)) - 1
  let M15 := rep32 (2 * m + 2) 32767
  let red3 := fun (x : Nat) => x - 3 * (((x * 43691) >>> 17) &&& M15)
  let G := red3 (2 * (Fl &&& ML))
  let nb := (3 ^ m).log2 + 1
  liftCoreM <| withOptions (Elab.async.set · false) do
    for (n, v) in [(`m, m), (`F, L.F), (`g, L.g), (`dg, L.dg), (`q1, q1), (`hf, L.hf),
        (`ET, packW 32 L.ET), (`ZT, packW 15 L.ZT), (`Fl, Fl), (`G, G), (`M15, M15), (`ML, ML),
        (`nb, nb)] do
      addDefE (P ++ n) nat (lit v)
    addThm (P ++ `head) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.headOK)
      #[c `m, c `F, c `g, c `dg, c `q1, c `hf, c `ET, c `ZT, lit 399])) reflBoolTrue
    let pre := #[c `m, c `F, c `g, c `dg, c `q1, c `ET]
    let mut ch : Array (Nat × Nat × Name) := #[]
    for (s, len) in chunks q1 1024 do
      let nm := P ++ Name.mkSimple s!"chain{s}"
      addThm nm (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.chainOK) (pre ++ #[lit s, lit len])))
        reflBoolTrue
      ch := ch.push (s, len, nm)
    addThm (P ++ `chainAll) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.chainOK)
        (pre ++ #[lit 0, c `q1])))
      (assemble pre ``CFSG.KC.Misc.Ree2.chainOK_append ``CFSG.KC.Misc.Ree2.chainOK_zero ch)
    let preZ := #[c `q1, c `ET, c `ZT]
    let mut zc : Array (Nat × Nat × Name) := #[]
    for (s, len) in chunks q1 1024 do
      let nm := P ++ Name.mkSimple s!"zech{s}"
      addThm nm (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.zechOK) (preZ ++ #[lit s, lit len])))
        reflBoolTrue
      zc := zc.push (s, len, nm)
    addThm (P ++ `zechAll) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.zechOK)
        (preZ ++ #[lit 0, c `q1])))
      (assemble preZ ``CFSG.KC.Misc.Ree2.zechOK_append ``CFSG.KC.Misc.Ree2.zechOK_zero zc)
    addThm (P ++ `lanes) (isTrue (mkApp2 (mkConst ``Nat.beq) (c `Fl)
      (mkApp2 (mkConst ``CFSG.KC.Misc.Ree2.lanesOf) (c `m) (c `F)))) reflBoolTrue
    addThm (P ++ `setup) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree.setupK)
      #[c `m, c `Fl, c `G, c `M15, c `ML])) reflBoolTrue
    addThm (P ++ `root) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree.rootK)
      #[c `m, c `G, c `M15, c `ML, c `nb])) reflBoolTrue

open CFSG.KC.Misc.Ree2Gen in
elab "#ree2_entry " pre:ident fd:ident kk:num ll:num ng:ident ws:num* : command => do
  let P := (← getCurrNamespace) ++ pre.getId
  let Fd ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent (fd.getId ++ `m)) <&> (·.getPrefix)
  let m ← liftCoreM <| readNat (Fd ++ `m)
  let F ← liftCoreM <| readNat (Fd ++ `F)
  let g ← liftCoreM <| readNat (Fd ++ `g)
  let k := kk.getNat
  let lam := ll.getNat
  let neg ← match ng.getId with
    | `true => pure true
    | `false => pure false
    | _ => throwError "neg must be true or false"
  let L ← match mkLF m F g with
    | .ok L => pure L
    | .error e => throwError e
  let q1 := L.q1
  let D := 114
  let W := ws.map fun w => let x := ofCodeMP w.getNat; if x == 0 then q1 else L.LG[L.idx x]!
  if W.size != k + 1 then throwError "expected k + 1 coordinates"
  let cs := (Array.range 5).map fun j =>
    L.pw (W.getD (CFSG.Walter.Ree.Bombieri.substIdx k neg j) q1)
      (3 ^ CFSG.Walter.Ree.Bombieri.substExp k lam neg j)
  let vars := fun (i : Nat) => cs.getD i q1
  for ε in [(0 : Int), 1, -1] do
    if L.eval vars (fun _ => q1) (CFSG.Walter.Ree.Bombieri.Elim.qExpr ε) == q1 then
      throwError s!"Q_{ε} vanishes"
  let mut xs : Array Nat := #[]
  let mut ys : Array Nat := #[]
  let mut ys' : Array Nat := #[]
  for x in [0:400] do
    if xs.size < D + 1 then
      match L.det cs[0]! cs[1]! cs[2]! cs[3]! x, L.det cs[1]! cs[2]! cs[3]! cs[4]! x with
      | some d, some d' =>
        xs := xs.push x
        ys := ys.push d
        ys' := ys'.push d'
      | _, _ => pure ()
  if xs.size < D + 1 then throwError "too few interpolation points"
  let p := L.interp xs ys
  let p' := L.interp xs ys'
  if p.size != D + 1 || p[D]! == q1 then throwError "leading coefficient vanishes"
  let ζ := L.add 0 (L.mul cs[1]! (L.mul cs[0]! cs[0]!))
  let p1 := (Array.range (2 * D + 1)).map fun n =>
    if n % 2 == 0 then L.mul p'[D - n / 2]! (L.pw ζ (D - n / 2)) else q1
  let (g, s, t) := L.pxgcd p p1
  if g.size != 1 || g[0]! == q1 then throwError "not coprime"
  if s.size == 0 || t.size == 0 || s.size > 2 * D || t.size > D then throwError "Bezout sizes"
  let lhs := L.trim (L.padd (L.pmul s p) (L.pmul t p1))
  if lhs != #[g[0]!] then throwError "Bezout identity fails in the twin"
  let nat := mkConst ``Nat
  let lnat := mkApp (mkConst ``List [0]) nat
  let c := fun (s : Name) => mkConst (P ++ s)
  let f := fun (s : Name) => mkConst (Fd ++ s)
  let negE := if neg then mkConst ``Bool.true else mkConst ``Bool.false
  let cE := fun (j : Nat) => mkAppN (mkConst ``CFSG.KC.Misc.Ree2.cpt)
    #[f `q1, c `W, lit k, lit lam, negE, lit j]
  let cArgs := (Array.range 5).map cE
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDefE (P ++ `W) lnat (natListE W)
    addDefE (P ++ `xs) lnat (natListE xs)
    addDefE (P ++ `p) lnat (natListE p)
    addDefE (P ++ `pp) lnat (natListE p')
    addDefE (P ++ `s) lnat (natListE s)
    addDefE (P ++ `t) lnat (natListE t)
    addDefE (P ++ `g0) nat (lit g[0]!)
    addThm (P ++ `q) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.qOK)
      (#[f `q1, f `hf, f `ZT] ++ cArgs))) reflBoolTrue
    let preI := #[f `q1, f `hf, f `ZT, mkConst ``CFSG.KC.Misc.Ree2.shapeL,
      mkConst ``CFSG.KC.Misc.Ree2.atomL, mkConst ``CFSG.KC.Misc.Ree2.coefL] ++ cArgs ++
      #[c `xs, c `p, c `pp]
    let mut ic : Array (Nat × Nat × Name) := #[]
    for (s0, len) in chunks (D + 1) 8 do
      let nm := P ++ Name.mkSimple s!"int{s0}"
      addThm nm (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.interpOK)
        (preI ++ #[lit s0, lit len]))) reflBoolTrue
      ic := ic.push (s0, len, nm)
    addThm (P ++ `intAll) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.interpOK)
        (preI ++ #[lit 0, lit (D + 1)])))
      (assemble preI ``CFSG.KC.Misc.Ree2.interpOK_append ``CFSG.KC.Misc.Ree2.interpOK_zero ic)
    addThm (P ++ `size) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.sizeOK)
      #[f `q1, lit D, c `p, c `pp, c `s, c `t, c `g0])) reflBoolTrue
    let P1E := mkAppN (mkConst ``CFSG.KC.Misc.Ree2.p1Pack) #[f `q1, lit D,
      mkAppN (mkConst ``CFSG.KC.Misc.Ree2.zetaL) #[f `q1, f `ZT, cArgs[0]!, cArgs[1]!], c `pp]
    let preB := #[f `q1, f `ZT, lit D, c `s, c `p, c `t, P1E, c `g0]
    let mut bc : Array (Nat × Nat × Name) := #[]
    for (s0, len) in chunks (3 * D + 1) 16 do
      let nm := P ++ Name.mkSimple s!"bez{s0}"
      addThm nm (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.bezOK) (preB ++ #[lit s0, lit len])))
        reflBoolTrue
      bc := bc.push (s0, len, nm)
    addThm (P ++ `bezAll) (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree2.bezOK)
        (preB ++ #[lit 0, lit (3 * D + 1)])))
      (assemble preB ``CFSG.KC.Misc.Ree2.bezOK_append ``CFSG.KC.Misc.Ree2.bezOK_zero bc)
  let hk := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit k) (lit 3) reflBoolTrue
  let hW := mkApp2 (mkConst ``Eq.refl [1]) nat (lit (k + 1))
  let pf := mkAppN (mkConst ``CFSG.KC.Misc.Ree2.entry_sound)
    #[f `m, f `F, f `g, f `dg, f `q1, f `hf, f `ET, f `ZT, f `Fl, f `G, f `M15, f `ML, f `nb,
      lit k, lit lam, negE, c `W, c `xs, c `p, c `pp, c `s, c `t, c `g0,
      f `head, f `chainAll, f `zechAll, f `lanes, f `setup, f `root, hk, hW, reflBoolTrue,
      c `q, reflBoolTrue, c `intAll, c `size, c `bezAll]
  let ty ← liftTermElabM <| do
    let t ← Meta.inferType pf
    instantiateMVars t
  liftCoreM <| withOptions (Elab.async.set · false) do
    addThm (P ++ `ok) ty pf
