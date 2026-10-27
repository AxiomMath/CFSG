module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Data.CFSGNative.SectionRank.Local
public meta import Certificates.Data.CFSGNative.SectionRank.LocalDet
public meta import Certificates.Data.CFSGNative.LQTFast
public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Data.CFSGNative.SectionRank.Elem3
public import Lean.Exception

public section

open Lean Elab Command Meta

namespace CFSG.KC.LQT.Cmd

meta def natE : Expr := mkConst ``Nat
meta def boolE : Expr := mkConst ``Bool
meta def lit (n : Nat) : Expr := mkRawNatLit n
meta def eqTrue (b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolE b (mkConst ``Bool.true)

meta def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

meta def addTrue (name : Name) (b : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name, levelParams := [], type := eqTrue b, value := reflBoolTrue }

meta def addThm (name : Name) (type value : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name, levelParams := [], type, value }

meta def withSync (x : CoreM Unit) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) x

structure LayV where
  p : Nat
  w : Nat
  S : Nat
  d : Nat
  T : Nat
  L : Nat
  H : Nat
  CM : Nat
  RM : Nat
  ONE : Nat
  LV : Nat
  HV : Nat

meta def rep1 (s n : Nat) : Nat := ((1 <<< (s * n)) - 1) / ((1 <<< s) - 1)

meta def layOf (p d : Nat) : LayV := Id.run do
  let mut w := 2
  while !(d * (p - 1) * (p - 1) < (1 <<< (w - 1))) do w := w + 1
  let mut T := 0
  while (p <<< (T + 1)) ≤ (1 <<< (w - 1)) do T := T + 1
  let S := d * w
  let L := rep1 w (d * d)
  let LV := rep1 w d
  return { p, w, S, d, T, L, H := L <<< (w - 1), CM := ((1 <<< w) - 1) * rep1 S d,
           RM := (1 <<< S) - 1, ONE := rep1 (S + w) d, LV, HV := LV <<< (w - 1) }

meta def LayV.csub (c : LayV) (L H k x : Nat) : Nat :=
  x - ((((x ||| H) - k * L) &&& H) >>> (c.w - 1)) * k

meta def LayV.red (c : LayV) (L H x : Nat) : Nat := Id.run do
  let mut x := x
  for i in [0:c.T + 1] do
    x := c.csub L H (c.p <<< (c.T - i)) x
  return x

meta def LayV.mul (c : LayV) (A B : Nat) : Nat := Id.run do
  if c.p == 3 then return CFSG.KC.LQT.Fast.mulPacked c.w c.d A B
  let mut acc := 0
  for k in [0:c.d] do
    acc := acc + ((A >>> (c.w * k)) &&& c.CM) * ((B >>> (c.S * k)) &&& c.RM)
  return c.red c.L c.H acc

meta def LayV.vec (c : LayV) (v M : Nat) : Nat := Id.run do
  let mut acc := 0
  let m := (1 <<< c.w) - 1
  for k in [0:c.d] do
    acc := acc + ((v >>> (c.w * k)) &&& m) * ((M >>> (c.S * k)) &&& c.RM)
  return c.red c.LV c.HV acc

meta def LayV.pow (c : LayV) (X e : Nat) : Nat := Id.run do
  let mut acc := c.ONE
  for _ in [0:e] do acc := c.mul acc X
  return acc

meta def LayV.vpow (c : LayV) (X v e : Nat) : Nat := Id.run do
  let mut acc := v
  for _ in [0:e] do acc := c.vec acc X
  return acc

meta def LayV.unit (c : LayV) (t : Nat) : Nat := 1 <<< (c.w * t)

meta def LayV.digApp (c : LayV) (b : Nat) (X : Array Nat) (n v : Nat) : Nat := Id.run do
  let mut n := n
  let mut v := v
  for x in X do
    v := c.vpow x v (n % b)
    n := n / b
  return v

meta def LayV.decode (c : LayV) (s : String) : Nat := Id.run do
  if c.p == 3 then return CFSG.KC.LQT.Fast.decodePacked c.w c.d s
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  let es := (body.filter fun ch => !(ch.toNat == 32 || (9 ≤ ch.toNat && ch.toNat ≤ 13))).map
    fun ch => if 48 ≤ ch.toNat && ch.toNat ≤ 57 then ch.toNat - 48 else 0
  let mut M := 0
  let mut k := 0
  for e in es do
    if k < c.d * c.d then
      M := M ||| ((e % c.p) <<< (c.S * (k / c.d) + c.w * (k % c.d)))
    k := k + 1
  return M

meta def LayV.expr (c : LayV) : Expr :=
  mkAppN (mkConst ``CFSG.KC.LQT.Lay.mk)
    #[lit c.p, lit c.w, lit c.S, lit c.d, lit c.T, lit c.L, lit c.H, lit c.CM, lit c.RM, lit c.ONE,
      lit c.LV, lit c.HV]

open CFSG.SectionRank.Native in
meta def ssa (c : LayV) (A B : Nat) (nregs : Nat) (prog : List Op) :
    Array Nat × Array (Nat × Nat) × Array Nat := Id.run do
  let mut vals : Array Nat := #[A, B, c.ONE]
  let mut ops : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0)]
  let mut regs : Array Nat := (Array.range nregs).map fun r => if r == 0 then 0 else if r == 1 then 1 else 2
  let mulI := fun (vals : Array Nat) (ops : Array (Nat × Nat)) (a b : Nat) =>
    match ops.findIdx? (· == (a, b)) with
    | some i => if i ≥ 3 then (vals, ops, i) else
        (vals.push (c.mul vals[a]! vals[b]!), ops.push (a, b), vals.size)
    | none => (vals.push (c.mul vals[a]! vals[b]!), ops.push (a, b), vals.size)
  for o in prog do
    match o with
    | .mul i j k =>
      let (v', o', r) := mulI vals ops regs[i]! regs[j]!
      vals := v'; ops := o'; regs := regs.set! k r
    | .pow e i k =>
      if e == 0 then regs := regs.set! k 2
      else
        let mut res : Option Nat := none
        let mut base := regs[i]!
        let mut e' := e
        while e' > 0 do
          if e' % 2 == 1 then
            match res with
            | none => res := some base
            | some r0 =>
              let (v', o', r) := mulI vals ops r0 base
              vals := v'; ops := o'; res := some r
          e' := e' / 2
          if e' > 0 then
            let (v', o', r) := mulI vals ops base base
            vals := v'; ops := o'; base := r
        regs := regs.set! k res.get!
  return (vals, ops, regs)

meta partial def addSel (F : Name) (leaf : Nat → Expr) (n : Nat) : CoreM Unit := do
  let d := max 1 (Nat.log2 (2 * n - 1))
  let rec go (lo hi b : Nat) : CoreM Unit := do
    if hi - lo ≤ 1 then return
    let mid := (lo + hi) / 2
    go lo mid (b - 1)
    go mid hi (b - 1)
    let child := fun l h =>
      if h - l == 1 then (if l < n then leaf l else lit 0)
      else mkApp (mkConst (F.appendAfter s!"_{l}_{b - 1}")) (.bvar 0)
    let bit := mkApp2 (mkConst ``Nat.blt) (lit 0) (mkApp2 (mkConst ``Nat.land) (.bvar 0) (lit (1 <<< b)))
    let body := mkApp4 (mkConst ``Bool.rec [1]) (mkLambda `x .default boolE natE)
      (child lo mid) (child mid hi) bit
    addDef (F.appendAfter s!"_{lo}_{b}") (mkForall `k .default natE natE)
      (mkLambda `k .default natE body)
  go 0 (1 <<< d) (d - 1)
  addDef F (mkForall `k .default natE natE)
    (mkLambda `k .default natE (mkApp (mkConst (F.appendAfter s!"_0_{d - 1}")) (.bvar 0)))

meta def natList (xs : List Nat) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natE (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natE)

meta partial def literalOf (n : Name) : CoreM String := do
  let some (.defnInfo v) := (← getEnv).find? n | throwError "{n} is not a definition"
  let rec go (e : Expr) : CoreM String := do
    match e.consumeMData with
    | .lit (.strVal s) => return s
    | e =>
      if e.isAppOfArity ``HAppend.hAppend 6 then
        return (← go (e.getArg! 4)) ++ (← go (e.getArg! 5))
      else if e.isAppOfArity ``String.append 2 then
        return (← go (e.getArg! 0)) ++ (← go (e.getArg! 1))
      else throwError "{n} is not a string literal or an append of literals: {e}"
  go v.value

meta def addChars (L seed : Name) : CoreM String := do
  let s ← literalOf seed
  let charT := mkConst ``Char
  let cons := mkApp (mkConst ``List.cons [0]) charT
  let cache : Array Expr := (Array.range 128).map fun i => mkApp (mkConst ``Char.ofNat) (lit i)
  let mut l := mkApp (mkConst ``List.nil [0]) charT
  for ch in s.toList.reverse do
    let e := if ch.toNat < 128 then cache[ch.toNat]! else mkApp (mkConst ``Char.ofNat) (lit ch.toNat)
    l := mkApp2 cons e l
  addDef L (mkApp (mkConst ``List [0]) charT) l
  let strT := mkConst ``String
  let ty := mkApp3 (mkConst ``Eq [1]) strT (mkConst seed) (mkApp (mkConst ``String.ofList) (mkConst L))
  addThm (L.appendAfter "_eq") ty (mkApp2 (mkConst ``Eq.refl [1]) strT (mkConst seed))
  let lc := mkApp (mkConst ``List [0]) charT
  let ofL := mkApp (mkConst ``String.ofList) (mkConst L)
  let toL := mkConst ``String.toList
  let ty2 := mkApp3 (mkConst ``Eq [1]) lc (mkApp toL (mkConst seed)) (mkConst L)
  let cg := mkAppN (mkConst ``congrArg [1, 1])
    #[strT, lc, mkConst seed, ofL, toL, mkConst (L.appendAfter "_eq")]
  let pf := mkAppN (mkConst ``Eq.trans [1])
    #[lc, mkApp toL (mkConst seed), mkApp toL ofL, mkConst L, cg,
      mkApp (mkConst ``String.toList_ofList) (mkConst L)]
  addThm (L.appendAfter "_toList") ty2 pf
  return s

elab "#lqt_chars " L:ident seed:ident : command =>
  withSync do discard <| addChars L.getId seed.getId

meta def addProgram (pre : Name) (p d : Nat) (seedA seedB : Name) (nregs : Nat)
    (prog : List CFSG.SectionRank.Native.Op)
    (extra : LayV → Array Nat → Array Nat → Array Nat := fun _ _ _ => #[]) :
    CoreM (LayV × Array Nat × Array Nat) := do
  let c := layOf p d
  let lay := mkConst (pre ++ `lay)
  addDef (pre ++ `lay) (mkConst ``CFSG.KC.LQT.Lay) c.expr
  addTrue (pre ++ `lay_ok) (mkApp (mkConst ``CFSG.KC.LQT.Lay.ok) lay)
  let sA ← addChars (pre ++ `LA) seedA
  let sB ← addChars (pre ++ `LB) seedB
  let A := c.decode sA
  let B := c.decode sB
  let (vals, ops, regs) := ssa c A B nregs prog
  let all := vals ++ extra c vals regs
  for k in [0:all.size] do
    addDef (pre ++ Name.mkSimple s!"V{k}") natE (lit all[k]!)
  addSel (pre ++ `V) (fun k => mkConst (pre ++ Name.mkSimple s!"V{k}")) all.size
  addDef (pre ++ `N) natE (lit vals.size)
  for k in [3:ops.size] do
    let (a, b) := ops[k]!
    addDef (pre ++ Name.mkSimple s!"P{k}") natE (lit (a + (b <<< 20)))
  addSel (pre ++ `P) (fun k => if k < 3 then lit 0 else mkConst (pre ++ Name.mkSimple s!"P{k}")) ops.size
  let V := mkConst (pre ++ `V)
  let P := mkConst (pre ++ `P)
  addTrue (pre ++ `decA) (mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay (mkApp V (lit 0)) (mkConst (pre ++ `LA)))
  addTrue (pre ++ `decB) (mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay (mkApp V (lit 1)) (mkConst (pre ++ `LB)))
  let oneTy := mkApp3 (mkConst ``Eq [1]) natE (mkApp V (lit 2)) (mkApp (mkConst ``CFSG.KC.LQT.Lay.ONE) lay)
  addThm (pre ++ `one) oneTy (mkApp2 (mkConst ``Eq.refl [1]) natE (mkApp V (lit 2)))
  let f := mkApp3 (mkConst ``CFSG.KC.LQT.stepOK) lay V P
  let mut pf := mkApp (mkConst ``CFSG.KC.LQT.steps_three) f
  for k in [3:ops.size] do
    let tn := pre ++ Name.mkSimple s!"s{k}"
    addTrue tn (mkApp f (lit k))
    pf := mkAppN (mkConst ``CFSG.KC.LQT.steps_succ) #[f, lit k, pf, mkConst tn]
  let stTy := mkApp2 (mkConst ``CFSG.KC.LQT.StepsTo) f (lit ops.size)
  addThm (pre ++ `steps) stTy pf
  return (c, vals, regs)

open CFSG.SectionRank.Native in
meta unsafe def evalData (n : Name) : CoreM Data := evalConst Data n

open CFSG.SectionRank.Native in
meta unsafe def evalSq (n : Name) : CoreM SqData := evalConst SqData n

open CFSG.SectionRank.Native in
meta unsafe def evalCub (n : Name) : CoreM CubData := evalConst CubData n

elab "#lqt_sr_elem " pre:ident dat:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalData dat.getId
  withSync do
    let (c, vals, regs) ← addProgram pre p.getNat d.getNat sA.getId sB.getId D.nregs D.prog
    let O := D.outs.map fun r => regs[r]!
    let X := (O.map fun i => vals[i]!).toArray
    let r := O.length
    let mut W : Array Nat := #[0]
    for n in [1:3 ^ r] do
      match D.tests.find? (fun t => t < c.d && c.digApp 3 X n (c.unit t) != c.unit t) with
      | some t => W := W.push t
      | none => throwError "no test vector moved by exponent code {n}"
    addSel (pre ++ `O) (fun i => lit O[i]!) r
    addSel (pre ++ `W) (fun n => lit W[n]!) W.size
    addTrue (pre ++ `elem) (mkAppN (mkConst ``CFSG.KC.LQT.elemOK)
      #[mkConst (pre ++ `lay), mkConst (pre ++ `V), lit vals.size, mkConst (pre ++ `O),
        mkConst (pre ++ `W), lit r])

meta def sortOrder (c : LayV) (b : Nat) (X : Array Nat) (t : Nat) : List Nat :=
  let N := b ^ X.size
  let vs := (List.range N).map fun n => (c.digApp b X n (c.unit t), n)
  (vs.mergeSort (fun a b => a.1 ≤ b.1)).map (·.2)

elab "#lqt_sr_sq " pre:ident dat:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalSq dat.getId
  withSync do
    let (c, vals, regs) ← addProgram pre p.getNat d.getNat sA.getId sB.getId D.nregs D.prog
    let ix := regs[D.rx]!
    let iy := regs[D.ry]!
    let ih := regs[D.rh]!
    for (nm, v) in [(`ix, ix), (`iy, iy), (`ih, ih)] do addDef (pre ++ nm) natE (lit v)
    let σ := sortOrder c D.r #[vals[ix]!, vals[iy]!] D.t
    addDef (pre ++ `sigma) (mkApp (mkConst ``List [0]) natE) (natList σ)
    addTrue (pre ++ `sq) (mkAppN (mkConst ``CFSG.KC.LQT.sqOK)
      #[mkConst (pre ++ `lay), mkConst (pre ++ `V), lit vals.size, lit ix, lit iy, lit ih, lit D.r,
        lit D.oh, lit D.a, lit D.b, lit D.c, lit D.d, lit D.t, mkConst (pre ++ `sigma)])

elab "#lqt_sr_cub " pre:ident dat:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalCub dat.getId
  withSync do
    let (c, vals, regs) ← addProgram pre p.getNat d.getNat sA.getId sB.getId D.nregs D.prog
    let ix := regs[D.rx]!
    let iy := regs[D.ry]!
    let ih := regs[D.rh]!
    for (nm, v) in [(`ix, ix), (`iy, iy), (`ih, ih)] do addDef (pre ++ nm) natE (lit v)
    let X := vals[ix]!
    let Y := vals[iy]!
    let Z := c.mul (c.mul (c.mul X Y) (c.pow X (D.r - 1))) (c.pow Y (D.r - 1))
    let σ := sortOrder c D.r #[X, Y, Z] D.t
    addDef (pre ++ `sigma) (mkApp (mkConst ``List [0]) natE) (natList σ)
    addTrue (pre ++ `cub) (mkAppN (mkConst ``CFSG.KC.LQT.cubOK)
      #[mkConst (pre ++ `lay), mkConst (pre ++ `V), lit vals.size, lit ix, lit iy, lit ih, lit D.r,
        lit D.oh, lit D.a, lit D.b, lit D.c, lit D.d, lit D.k, lit D.l, lit D.μ, lit D.t,
        mkConst (pre ++ `sigma)])

open CFSG.SectionRank.Native in
meta unsafe def evalLoc (n : Name) : CoreM LocDetData := evalConst LocDetData n

meta def enumK (c : LayV) (K1 K2 : Nat) (cap : Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let mut E : Array Nat := #[c.ONE]
  let mut PL : Array Nat := #[0]
  let mut idx : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert c.ONE 0
  let mut CL : Array Nat := #[]
  let mut h := 0
  while h < E.size && h < cap do
    for (g, l) in [(K1, 0), (K2, 1)] do
      let Y := c.mul E[h]! g
      match idx.get? Y with
      | some j => CL := CL.push j
      | none =>
        CL := CL.push E.size
        idx := idx.insert Y E.size
        E := E.push Y
        PL := PL.push (h + (l <<< 20))
    h := h + 1
  return (E, PL, CL)

elab "#lqt_sr_locdet " pre:ident dat:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalLoc dat.getId
  withSync do
    let enumOf := fun (c : LayV) (vals regs : Array Nat) =>
      (enumK c vals[regs[D.rk1]!]! vals[regs[D.rk2]!]! (D.nK + 1)).1
    let (c, vals, regs) ← addProgram pre p.getNat d.getNat sA.getId sB.getId D.nregs D.prog enumOf
    let N := vals.size
    let (E, PL, CL) := enumK c vals[regs[D.rk1]!]! vals[regs[D.rk2]!]! (D.nK + 1)
    unless E.size == D.nK do throwError "enumeration has {E.size} elements, expected {D.nK}"
    let ri := #[D.rk1, D.rk2, D.rx, D.ry, D.rh, D.rc, D.ru1, D.rv1, D.ru2, D.rv2].map (regs[·]!)
    let pos := fun (X : Nat) => (E.findIdx? (· == X)).getD E.size
    let vI := fun k => vals[ri[k]!]!
    let H := vI 4
    let posConj := fun (K : Nat) => (E.findIdx? (fun Z => c.mul H K == c.mul Z H)).getD E.size
    let I := ri ++ #[pos (vI 2), pos (vI 3), pos (vI 6), pos (vI 7), pos (vI 8), pos (vI 9),
      posConj (vI 0), posConj (vI 1)]
    addSel (pre ++ `I) (fun k => lit I[k]!) I.size
    addSel (pre ++ `PL) (fun k => lit PL[k]!) PL.size
    addSel (pre ++ `CL) (fun k => lit CL[k]!) CL.size
    let unitT := c.unit D.t
    let σq := sortOrder c 3 #[vI 2, vI 3] D.t
    let σe := ((List.range E.size).map (fun i => (c.vec unitT E[i]!, i))).mergeSort
      (fun a b => a.1 ≤ b.1) |>.map (·.2)
    addDef (pre ++ `sigmaQ) (mkApp (mkConst ``List [0]) natE) (natList σq)
    addDef (pre ++ `sigmaE) (mkApp (mkConst ``List [0]) natE) (natList σe)
    let Ef := mkLambda `i .default natE (mkApp2 (mkConst ``Nat.add) (lit N) (.bvar 0))
    addDef (pre ++ `E) (mkForall `i .default natE natE) Ef
    addTrue (pre ++ `loc) (mkAppN (mkConst ``CFSG.KC.LQT.locOK)
      #[mkConst (pre ++ `lay), mkConst (pre ++ `V), mkConst (pre ++ `I), mkConst (pre ++ `E),
        mkConst (pre ++ `PL), mkConst (pre ++ `CL), lit N, lit D.nK, lit D.t, lit D.ok1, lit D.ok2,
        lit D.oh, lit D.a, lit D.b, lit D.c, lit D.d, mkConst (pre ++ `sigmaQ),
        mkConst (pre ++ `sigmaE)])

end CFSG.KC.LQT.Cmd

end
