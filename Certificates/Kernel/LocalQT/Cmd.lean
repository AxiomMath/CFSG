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

meta def litChunks (n : Nat) : Array Nat := Id.run do
  let k0 := Nat.log2 (n.log2 / 8192) + 1
  let masks := (Array.range k0).map fun k => (1 <<< (8192 <<< k)) - 1
  let rec go : Nat → Nat → Array Nat → Array Nat
    | 0, m, acc => acc.push m
    | k + 1, m, acc => go k (m >>> (8192 <<< k)) (go k (m &&& masks[k]!) acc)
  let mut cs := go k0 n #[]
  while cs.size > 1 && cs.back! == 0 do
    cs := cs.pop
  return cs

meta def bigLit (n : Nat) : Expr :=
  if n < 1 <<< 16384 then mkRawNatLit n else
    let cs := litChunks n
    let salt (c i : Nat) : Nat :=
      (c % 2305843009213693951 * 11400714819323198485 + (i + 1) * 14029467366897019727) % (1 <<< 64)
    let ls := (Array.range cs.size).map fun i => mkApp2 (mkConst ``Nat.shiftRight)
      (mkRawNatLit ((cs[i]! <<< 64) ||| salt cs[i]! i)) (mkRawNatLit 64)
    let rec tree : Nat → Nat → Nat → Expr
      | 0, lo, _ => ls[lo]!
      | f + 1, lo, hi =>
        if hi ≤ lo + 1 then ls[lo]! else
          let mid := (lo + hi) / 2
          mkApp2 (mkConst ``Nat.lor) (tree f lo mid)
            (mkApp2 (mkConst ``Nat.shiftLeft) (tree f mid hi) (mkRawNatLit (8192 * (mid - lo))))
    tree (cs.size.log2 + 2) 0 cs.size

meta partial def natOfLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal x) => some x
  | e =>
    let op? : Option (Nat → Nat → Nat) :=
      if e.isAppOfArity ``Nat.lor 2 then some (· ||| ·)
      else if e.isAppOfArity ``Nat.shiftLeft 2 then some (· <<< ·)
      else if e.isAppOfArity ``Nat.shiftRight 2 then some (· >>> ·)
      else none
    match op? with
    | some op => do return op (← natOfLit? e.appFn!.appArg!) (← natOfLit? e.appArg!)
    | none => none
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

meta def LayV.rowsOf (c : LayV) (A : Nat) : Nat × Array CFSG.F3.Native.V :=
  (A, if c.p == 3 then CFSG.KC.LQT.Fast.toRows c.w c.d A else #[])

meta def LayV.mulRows (c : LayV) (A B : Nat × Array CFSG.F3.Native.V) :
    Nat × Array CFSG.F3.Native.V :=
  if A.1 == c.ONE then B else if B.1 == c.ONE then A else
  if c.p == 3 then
    let R := CFSG.F3.Native.mul c.d A.2 B.2
    (CFSG.KC.LQT.Fast.ofRows c.w c.d R, R)
  else (c.mul A.1 B.1, #[])

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
    #[lit c.p, lit c.w, lit c.S, lit c.d, lit c.T, bigLit c.L, bigLit c.H, bigLit c.CM, bigLit c.RM,
      bigLit c.ONE, bigLit c.LV, bigLit c.HV]

open CFSG.SectionRank.Native in
meta def ssa (c : LayV) (A B : Nat) (nregs : Nat) (prog : List Op) :
    Array Nat × Array (Nat × Nat) × Array Nat := Id.run do
  let mut vals : Array (Nat × Array CFSG.F3.Native.V) := #[c.rowsOf A, c.rowsOf B, (c.ONE, #[])]
  let mut ops : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0)]
  let mut regs : Array Nat := (Array.range nregs).map fun r => if r == 0 then 0 else if r == 1 then 1 else 2
  let mulI := fun (vals : Array (Nat × Array CFSG.F3.Native.V)) (ops : Array (Nat × Nat))
      (a b : Nat) =>
    match ops.findIdx? (· == (a, b)) with
    | some i => if i ≥ 3 then (vals, ops, i) else
        (vals.push (c.mulRows vals[a]! vals[b]!), ops.push (a, b), vals.size)
    | none => (vals.push (c.mulRows vals[a]! vals[b]!), ops.push (a, b), vals.size)
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
  return (vals.map (·.1), ops, regs)

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
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natE (bigLit x) acc)
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

meta def seedRoot (seed : Name) : Name := `CFSG.KD.SeedDec ++ seed

meta def seedDecRoot (seed : Name) (p d : Nat) : Name :=
  seedRoot seed ++ Name.mkSimple s!"p{p}d{d}"

meta def addCharsCut (L seed : Name) (cut : Nat) : CoreM (String × Array Expr) := do
  let s ← literalOf seed
  let charT := mkConst ``Char
  let cons := mkApp (mkConst ``List.cons [0]) charT
  let cache : Array Expr := (Array.range 128).map fun i => mkApp (mkConst ``Char.ofNat) (lit i)
  let cs := s.toList.toArray
  let mut l := mkApp (mkConst ``List.nil [0]) charT
  let mut sufs : Array Expr := #[]
  for q' in [0:cs.size] do
    let q := cs.size - 1 - q'
    let ch := cs[q]!
    let e := if ch.toNat < 128 then cache[ch.toNat]! else mkApp (mkConst ``Char.ofNat) (lit ch.toNat)
    l := mkApp2 cons e l
    if cut > 0 && q % cut == 0 then sufs := sufs.push l
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
  return (s, sufs.reverse)

meta def addChars (L seed : Name) : CoreM String := do
  let R := seedRoot seed
  if (← getEnv).contains (R ++ `L_toList) then
    let lc := mkApp (mkConst ``List [0]) (mkConst ``Char)
    let strT := mkConst ``String
    addDef L lc (mkConst (R ++ `L))
    addThm (L.appendAfter "_eq") (mkApp3 (mkConst ``Eq [1]) strT (mkConst seed)
      (mkApp (mkConst ``String.ofList) (mkConst L))) (mkConst (R ++ `L_eq))
    addThm (L.appendAfter "_toList") (mkApp3 (mkConst ``Eq [1]) lc
      (mkApp (mkConst ``String.toList) (mkConst seed)) (mkConst L)) (mkConst (R ++ `L_toList))
    return (← literalOf seed)
  return (← addCharsCut L seed 0).1

meta def addDecOK (name : Name) (c : LayV) (lay V : Expr) (v : Nat) (LA : Name) : CoreM Unit := do
  let b := mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay V (mkConst LA)
  let env ← getEnv
  let shared? : Option Name := match env.find? LA with
    | some (.defnInfo d) => match d.value with
      | .const X _ =>
        if X.isStr && X.getString! == "L" then
          let R := X.getPrefix ++ Name.mkSimple s!"p{c.p}d{c.d}"
          match env.find? (R ++ `M), env.find? (R ++ `lay) with
          | some (.defnInfo m), some (.defnInfo l) =>
            if m.value == lit v && l.value == c.expr && env.contains (R ++ `ok) then some R
            else none
          | _, _ => none
        else none
      | _ => none
    | _ => none
  match shared? with
  | some R => addThm name (eqTrue b) (mkConst (R ++ `ok))
  | none => addTrue name b

elab "#lqt_chars " L:ident seed:ident : command =>
  withSync do discard <| addChars L.getId seed.getId

meta def addProgram (pre : Name) (p d : Nat) (seedA seedB : Name) (nregs : Nat)
    (prog : List CFSG.SectionRank.Native.Op)
    (extra : LayV → Array Nat → Array Nat → Array Nat := fun _ _ _ => #[]) (f3 : Bool := false) :
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
  addDecOK (pre ++ `decA) c lay (mkApp V (lit 0)) A (pre ++ `LA)
  addDecOK (pre ++ `decB) c lay (mkApp V (lit 1)) B (pre ++ `LB)
  let oneTy := mkApp3 (mkConst ``Eq [1]) natE (mkApp V (lit 2)) (mkApp (mkConst ``CFSG.KC.LQT.Lay.ONE) lay)
  addThm (pre ++ `one) oneTy (mkApp2 (mkConst ``Eq.refl [1]) natE (mkApp V (lit 2)))
  let f := mkApp3 (mkConst ``CFSG.KC.LQT.stepOK) lay V P
  let stTy := mkApp2 (mkConst ``CFSG.KC.LQT.StepsTo) f (lit ops.size)
  if f3 && c.p == 3 then
    let K := Nat.log2 (c.d * c.d - 1) + 1
    let fld (f : Name) := mkApp (mkConst (``CFSG.KC.LQT.Lay ++ f)) lay
    let dS := mkAppN (mkConst ``HMul.hMul [0, 0, 0]) #[natE, natE, natE,
      mkApp2 (mkConst ``instHMul [0]) natE (mkConst ``instMulNat), fld `d, fld `S]
    let valid (k : Nat) := mkAppN (mkConst `CFSG.KC.Ord.validM)
      #[fld `p, dS, fld `L, fld `H, mkApp V (lit k)]
    addTrue (pre ++ `vA) (valid 0)
    addTrue (pre ++ `vB) (valid 1)
    let g := mkAppN (mkConst `CFSG.KC.LQT.stepF3)
      #[lay, lit K, mkApp2 (mkConst `CFSG.KS.F3L.spreadE) (fld `d) (fld `d), V, P]
    let mut pg := mkApp (mkConst ``CFSG.KC.LQT.steps_three) g
    for k in [3:ops.size] do
      let tn := pre ++ Name.mkSimple s!"s{k}"
      addTrue tn (mkApp g (lit k))
      pg := mkAppN (mkConst ``CFSG.KC.LQT.steps_succ) #[g, lit k, pg, mkConst tn]
    addThm (pre ++ `steps3) (mkApp2 (mkConst ``CFSG.KC.LQT.StepsTo) g (lit ops.size)) pg
    addThm (pre ++ `steps) stTy (mkAppN (mkConst `CFSG.KC.LQT.F3S.steps_of_F3V)
      #[lay, mkConst (pre ++ `lay_ok), reflBoolTrue, lit K, reflBoolTrue, reflBoolTrue, V, P,
        lit ops.size, mkConst (pre ++ `vA), mkConst (pre ++ `vB), mkConst (pre ++ `one),
        mkConst (pre ++ `steps3)])
  else
    let mut pf := mkApp (mkConst ``CFSG.KC.LQT.steps_three) f
    for k in [3:ops.size] do
      let tn := pre ++ Name.mkSimple s!"s{k}"
      addTrue tn (mkApp f (lit k))
      pf := mkAppN (mkConst ``CFSG.KC.LQT.steps_succ) #[f, lit k, pf, mkConst tn]
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

theorem sqMulEq {c : Lay} {A B A' B' M : Nat} (hA : A = A') (hB : B = B')
    (h : Nat.beq (c.mul A' B') M = true) : c.mul A B = M := by
  subst hA hB
  exact Nat.eq_of_beq_eq_true h

theorem sqPowEq {c : Lay} {X e A M : Nat} (h : c.pow X e = A)
    (hm : Nat.beq (c.mul A X) M = true) : c.pow X (Nat.succ e) = M := by
  change c.mul (c.pow X e) X = M
  rw [h]
  exact Nat.eq_of_beq_eq_true hm

theorem sqPow0 (c : Lay) (X : Nat) : c.pow X 0 = c.ONE := rfl

open CFSG.KC.Ord in
theorem sqOKParts {c : Lay} {V : Nat → Nat} {N ix iy ih r oh a b cc dd t : Nat} {σ : List Nat}
    {PX PY PH XY YX HX WX HY WY : Nat}
    (hpx : c.pow (V ix) r = PX) (hpy : c.pow (V iy) r = PY) (hph : c.pow (V ih) oh = PH)
    (hxy : c.mul (V ix) (V iy) = XY) (hyx : c.mul (V iy) (V ix) = YX)
    (hhx : c.mul (V ih) (V ix) = HX)
    (hwx : c.mul (c.mul (c.pow (V ix) a) (c.pow (V iy) cc)) (V ih) = WX)
    (hhy : c.mul (V ih) (V iy) = HY)
    (hwy : c.mul (c.mul (c.pow (V ix) b) (c.pow (V iy) dd)) (V ih) = WY)
    (hb : andB (Nat.blt ix N) (andB (Nat.blt iy N) (andB (Nat.blt ih N)
      (andB (Nat.blt (nat_lit 0) r) (andB (Nat.blt (nat_lit 0) oh)
      (andB (Nat.beq PX c.ONE) (andB (Nat.beq PY c.ONE) (andB (Nat.beq PH c.ONE)
      (andB (Nat.beq XY YX) (andB (Nat.beq HX WX) (andB (Nat.beq HY WY)
        (normalOK c r (sel3 (V ix) (V iy) (V iy)) (nat_lit 2) t σ))))))))))) = true) :
    sqOK c V N ix iy ih r oh a b cc dd t σ = true := by
  unfold sqOK conjOK
  rw [hpx, hpy, hph, hxy, hyx, hhx, hwx, hhy, hwy]
  exact hb

meta def addSq (pre : Name) (c : LayV) (vals : Array Nat) (ix iy ih r oh a b cc dd t : Nat) :
    CoreM Unit := do
  let lay := mkConst (pre ++ `lay)
  let Vc := mkConst (pre ++ `V)
  let one := mkApp (mkConst ``CFSG.KC.LQT.Lay.ONE) lay
  let f3 := c.p == 3
  let K := Nat.log2 (c.d * c.d - 1) + 1
  let fld (f : Name) := mkApp (mkConst (``CFSG.KC.LQT.Lay ++ f)) lay
  let dS := mkAppN (mkConst ``HMul.hMul [0, 0, 0]) #[natE, natE, natE,
    mkApp2 (mkConst ``instHMul [0]) natE (mkConst ``instMulNat), fld `d, fld `S]
  let vmemo ← IO.mkRef (∅ : Std.HashMap Expr Expr)
  let validT : Expr → CoreM Expr := fun e => do
    if let some h := (← vmemo.get)[e]? then return h
    let j := (← vmemo.get).size
    let n := pre ++ Name.mkSimple s!"qv{j}"
    addTrue n (mkAppN (mkConst `CFSG.KC.Ord.validM) #[fld `p, dS, fld `L, fld `H, e])
    vmemo.modify (·.insert e (mkConst n))
    return mkConst n
  let gath (e : Expr) := mkApp3 (mkConst `CFSG.KC.LQT.gath3) (fld `w) (lit K) e
  let M : Type := Nat × Array CFSG.F3.Native.V
  let canon ← IO.mkRef ((∅ : Std.HashMap Nat Expr).insert c.ONE one)
  let memo ← IO.mkRef (∅ : Std.HashMap (Expr × Expr) (M × Expr × Expr))
  let cnt ← IO.mkRef 0
  let mulE : M × Expr → M × Expr → CoreM (M × Expr × Expr) := fun (va, ea) (vb, eb) => do
    if let some res := (← memo.get)[(ea, eb)]? then return res
    let vr := c.mulRows va vb
    let v := vr.1
    let k ← cnt.modifyGet fun k => (k, k + 1)
    let em ← match (← canon.get)[v]? with
      | some e => pure e
      | none => do
        addDef (pre ++ Name.mkSimple s!"Q{k}") natE (lit v)
        let e := mkConst (pre ++ Name.mkSimple s!"Q{k}")
        canon.modify (·.insert v e)
        pure e
    let tn := pre ++ Name.mkSimple s!"q{k}"
    let qTy := mkApp2 (mkConst ``Nat.beq) (mkApp3 (mkConst ``CFSG.KC.LQT.Lay.mul) lay ea eb) em
    if f3 then
      let wa ← validT ea
      let wb ← validT eb
      let wm ← validT em
      let fn := pre ++ Name.mkSimple s!"qf{k}"
      addTrue fn (mkApp2 (mkConst `CFSG.KC.LQT.eqV) (gath em)
        (mkApp4 (mkConst `CFSG.KS.F3L.mulLane) (fld `d)
          (mkApp2 (mkConst `CFSG.KS.F3L.spreadE) (fld `d) (fld `d)) (gath ea) (gath eb)))
      addThm tn (eqTrue qTy) (mkAppN (mkConst `CFSG.KC.LQT.F3S.mul_of_F3V)
        #[lay, mkConst (pre ++ `lay_ok), reflBoolTrue, lit K, reflBoolTrue, reflBoolTrue, ea, eb, em,
          wa, wb, wm, mkConst fn])
    else
      addTrue tn qTy
    let res := (vr, em, mkConst tn)
    memo.modify (·.insert (ea, eb) res)
    return res
  let atom : Nat → CoreM (M × Expr × Expr × Expr) := fun i => do
    let v := vals[i]!
    let e := mkApp Vc (lit i)
    canon.modify fun m => if m.contains v then m else m.insert v e
    return (c.rowsOf v, e, e, mkApp2 (mkConst ``Eq.refl [1]) natE e)
  let powE : M × Expr × Expr × Expr → Nat → CoreM (M × Expr × Expr × Expr) :=
    fun (vx, ex, _, _) n => do
      let mut cur : M × Expr := ((c.ONE, #[]), one)
      let mut pf := mkApp2 (mkConst ``sqPow0) lay ex
      let mut eE := lit 0
      for _ in [0:n] do
        let (vm, em, hm) ← mulE cur (vx, ex)
        pf := mkAppN (mkConst ``sqPowEq) #[lay, ex, eE, cur.2, em, pf, hm]
        eE := mkApp (mkConst ``Nat.succ) eE
        cur := (vm, em)
      return (cur.1, cur.2, mkApp3 (mkConst ``CFSG.KC.LQT.Lay.pow) lay ex (lit n), pf)
  let mulT : M × Expr × Expr × Expr → M × Expr × Expr × Expr →
      CoreM (M × Expr × Expr × Expr) := fun (v1, e1, o1, p1) (v2, e2, o2, p2) => do
    let (vm, em, hm) ← mulE (v1, e1) (v2, e2)
    return (vm, em, mkApp3 (mkConst ``CFSG.KC.LQT.Lay.mul) lay o1 o2,
      mkAppN (mkConst ``sqMulEq) #[lay, o1, o2, e1, e2, em, p1, p2, hm])
  let X ← atom ix
  let Y ← atom iy
  let H ← atom ih
  let px ← powE X r
  let py ← powE Y r
  let ph ← powE H oh
  let xy ← mulT X Y
  let yx ← mulT Y X
  let hx ← mulT H X
  let wx ← mulT (← mulT (← powE X a) (← powE Y cc)) H
  let hy ← mulT H Y
  let wy ← mulT (← mulT (← powE X b) (← powE Y dd)) H
  let parts := #[px, py, ph, xy, yx, hx, wx, hy, wy]
  let base := #[lay, Vc, lit vals.size, lit ix, lit iy, lit ih, lit r, lit oh, lit a, lit b,
    lit cc, lit dd, lit t, mkConst (pre ++ `sigma)]
  let args := base ++ parts.map (·.2.1) ++ parts.map (·.2.2.2)
  let ty := args.foldl (fun T x => match T with
    | .forallE _ _ body _ => body.instantiate1 x
    | T => T) (← getConstInfo ``sqOKParts).type
  let .forallE _ hbTy _ _ := ty | throwError "addSq: unexpected type of sqOKParts"
  CFSG.KC.addThmDecl { name := pre ++ `sqR, levelParams := [], type := hbTy, value := reflBoolTrue }
  addThm (pre ++ `sq) (eqTrue (mkAppN (mkConst ``CFSG.KC.LQT.sqOK) base))
    (mkAppN (mkConst ``sqOKParts) (args.push (mkConst (pre ++ `sqR))))

elab "#lqt_sr_sq " pre:ident dat:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalSq dat.getId
  withSync do
    let (c, vals, regs) ← addProgram pre p.getNat d.getNat sA.getId sB.getId D.nregs D.prog
      (f3 := true)
    let ix := regs[D.rx]!
    let iy := regs[D.ry]!
    let ih := regs[D.rh]!
    for (nm, v) in [(`ix, ix), (`iy, iy), (`ih, ih)] do addDef (pre ++ nm) natE (lit v)
    let σ := sortOrder c D.r #[vals[ix]!, vals[iy]!] D.t
    addDef (pre ++ `sigma) (mkApp (mkConst ``List [0]) natE) (natList σ)
    addSq pre c vals ix iy ih D.r D.oh D.a D.b D.c D.d D.t

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
