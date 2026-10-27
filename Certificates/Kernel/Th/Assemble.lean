module

public import Certificates.Kernel.Th.Append
public import CFSG.Certificates.Kernel.Th.Gen.Wrap
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
meta import Certificates.Kernel.Co2.Join
public import Lean.Elab.Command

open Lean Elab Command

namespace CertificateChecks.KernelTh.Assemble

meta partial def normLits (e : Expr) : Expr :=
  e.replace fun x =>
    match x with
    | .mdata _ b => some (normLits b)
    | _ =>
      if x.isAppOfArity ``OfNat.ofNat 3 && (x.getArg! 0).consumeMData.isConstOf ``Nat then
        match (x.getArg! 1).consumeMData with
        | .lit (.natVal n) => some (mkRawNatLit n)
        | _ => none
      else none

meta def hole (f : Name) : Expr := mkMVar ⟨`_thAssemble ++ f⟩

meta partial def matchE (p e : Expr) (σ : Std.HashMap Name Expr) : Option (Std.HashMap Name Expr) :=
  if !p.hasMVar then (if p == e then some σ else none) else
  match p, e with
  | .mvar m, _ =>
    match σ[m.name]? with
    | some v => if v == e then some σ else none
    | none => some (σ.insert m.name e)
  | .app f a, .app g b => do
    let σ ← matchE f g σ
    matchE a b σ
  | .lam _ t b _, .lam _ t' b' _ => do
    let σ ← matchE t t' σ
    matchE b b' σ
  | .forallE _ t b _, .forallE _ t' b' _ => do
    let σ ← matchE t t' σ
    matchE b b' σ
  | .mdata _ q, _ => matchE q e σ
  | _, _ => none

meta def subst (σ : Std.HashMap Name Expr) (p : Expr) : Expr :=
  if !p.hasMVar then p else
  p.replace fun x => match x with
    | .mvar m => σ[m.name]?
    | _ => none

meta partial def atoms (t pf : Expr) : Array (Expr × Expr) :=
  if t.isAppOfArity ``CFSG.KC.Th.andB 2 then
    let a := t.getArg! 0
    let b := t.getArg! 1
    atoms a (mkApp3 (mkConst ``CFSG.KC.Th.Gen.andB_left) a b pf) ++
      atoms b (mkApp3 (mkConst ``CFSG.KC.Th.Gen.andB_right) a b pf)
  else
    let wrap (w lem : Name) (a b : Expr) : Array (Expr × Expr) :=
      #[(mkApp2 (mkConst w) a b, mkApp3 (mkConst lem) a b pf)]
    if t.isAppOfArity ``Nat.beq 2 then wrap ``CFSG.KC.Th.Gen.eqN ``CFSG.KC.Th.Gen.eqN_of (t.getArg! 0) (t.getArg! 1)
    else if t.isAppOfArity ``Nat.blt 2 then
      wrap ``CFSG.KC.Th.Gen.ltN ``CFSG.KC.Th.Gen.ltN_of (t.getArg! 0) (t.getArg! 1)
    else if t.isAppOfArity ``Nat.ble 2 then
      wrap ``CFSG.KC.Th.Gen.leN ``CFSG.KC.Th.Gen.leN_of (t.getArg! 0) (t.getArg! 1)
    else if (t.isAppOfArity ``CFSG.KC.Th.BigS.notB 1 || t.isAppOfArity ``CFSG.KC.Th.DceS.notB 1) &&
        (t.getArg! 0).isAppOfArity ``Nat.beq 2 then
      let lem := if t.isAppOfArity ``CFSG.KC.Th.BigS.notB 1 then ``CFSG.KC.Th.Gen.neN_of
        else ``CFSG.KC.Th.Gen.neN_of'
      wrap ``CFSG.KC.Th.Gen.neN lem ((t.getArg! 0).getArg! 0) ((t.getArg! 0).getArg! 1)
    else #[(t, pf)]

meta partial def segs : List String → List (List String)
  | [] => [[]]
  | [p] => [[p]]
  | p :: q :: rest => (segs (q :: rest)).map (p :: ·) ++ segs ((p ++ "_" ++ q) :: rest)

meta def kdConst (env : Environment) (f : String) : Except String Name := do
  let cands := (segs (f.splitOn "_")).filterMap fun cs =>
    let n := cs.foldl (fun n c => Name.str n c) `CFSG.KD
    if env.contains n then some n else none
  match cands.eraseDups with
  | [n] => return n
  | [] => throw s!"field {f}: no constant CFSG.KD.…"
  | ns => throw s!"field {f}: several constants {ns}"

meta def isFound (f : String) : Bool :=
  let num (p : String) := f.startsWith p && f.length > p.length && (f.drop p.length).all Char.isDigit
  num "cs" || num "sf" || num "l"

structure Index where
  slices : Std.HashMap (Expr × Expr) (Name × Expr × Expr) := {}
  exact : Std.HashMap Expr Expr := {}
  all : Array (Expr × Expr) := #[]
  laws : Std.HashMap Name Name := {}

meta def lawHead (ty : Expr) : Option Name := do
  let mut t := ty
  while t.isForall do t := t.bindingBody!
  let some (_, lhs, _) := t.eq? | none
  let n := lhs.getAppNumArgs
  guard (n ≥ 2)
  guard ((lhs.getArg! (n - 2)).isAppOfArity ``List.append 3)
  lhs.getAppFn.constName?

meta def buildIndex (env : Environment) : Index := Id.run do
  let mut ix : Index := {}
  for (n, ci) in env.constants.toList do
    unless ci matches .thmInfo _ || ci matches .axiomInfo _ do continue
    let ti := ci.toConstantVal
    if (`CFSG.KD).isPrefixOf n then
      let some (_, t, r) := ti.type.eq? | continue
      unless r.isConstOf ``Bool.true do continue
      if let some (f, l, x, y) := CertificateChecks.KernelCo2.Join.parts ti.type then
        unless ix.slices.contains (f, x) do ix := { ix with slices := ix.slices.insert (f, x) (n, l, y) }
      for (a, p) in atoms t (mkConst n) do
        unless ix.exact.contains a do ix := { ix with exact := ix.exact.insert a p }
        ix := { ix with all := ix.all.push (a, p) }
    else if (`CertificateChecks).isPrefixOf n || (`Certificates).isPrefixOf n then
      if let .str _ s := n then
        if s.endsWith "_append" then
          if let some h := lawHead ti.type then
            ix := { ix with laws := ix.laws.insert h n }
  return ix

structure St where
  σ : Std.HashMap Name Expr := {}
  loops : Nat := 0

abbrev M := StateT St CommandElabM

meta def addThm (nm : Name) (ty val : Expr) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) <|
    CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := val }

meta def addDefn (nm : Name) (ty val : Expr) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) <|
    addDecl <| .defnDecl
      { name := nm, levelParams := [], type := ty, value := val, hints := .regular 0, safety := .safe }

meta def boolEq (t : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) t (mkConst ``Bool.true)

meta partial def go (ix : Index) (pre : String) (ns : Name) (c : Expr) : M (Expr × Expr) := do
  if c.isAppOfArity ``CFSG.KC.Th.andB 2 then
    let (ta, pa) ← go ix pre ns (c.getArg! 0)
    let (tb, pb) ← go ix pre ns (c.getArg! 1)
    return (mkApp2 (mkConst ``CFSG.KC.Th.andB) ta tb,
      mkAppN (mkConst ``CertificateChecks.KernelTh.andB_true) #[ta, tb, pa, pb])
  let c := subst (← get).σ c
  let n := if c.isAppOfArity ``CFSG.KC.Th.Gen.eqN 2 then (c.getArg! 0).getAppNumArgs else 0
  let a := if n ≥ 2 then c.getArg! 0 else c
  let isCs (e : Expr) : Bool := match e with
    | .mvar m => match m.name with
      | .str _ s => s.startsWith "cs"
      | _ => false
    | _ => false
  if n ≥ 2 && isCs (a.getArg! (n - 2)) then
    let csH := (a.getArg! (n - 2)).mvarId!.name
    let F := mkAppN a.getAppFn (a.getAppArgs.extract 0 (n - 2))
    let x0 := a.getArg! (n - 1)
    let Y := c.getArg! 1
    if F.hasMVar || x0.hasMVar then throwError "loop with an unbound field{indentExpr c}"
    let mut sl : Array (Expr × Expr × Expr × Expr) := #[]
    let mut x := x0
    let mut names : Array Name := #[]
    repeat
      match ix.slices[(F, x)]? with
      | none => break
      | some (t, l, y) =>
        sl := sl.push (mkConst t, l, x, y)
        names := names.push t
        x := y
        if !Y.isMVar && y == Y then break
        if sl.size > 100000 then throwError "loop does not end{indentExpr c}"
    if sl.isEmpty then throwError "no slice of the loop{indentExpr c}"
    if !Y.isMVar && x != Y then throwError "the slices of the loop end at {x}{indentExpr c}"
    let i := (← get).loops
    modify fun s => { s with loops := i + 1 }
    let (p, L) ← if sl.size == 1 then pure (sl[0]!.1, sl[0]!.2.1) else do
      let some h := F.getAppFn.constName? | throwError "loop function without a head constant"
      let some law := ix.laws[h]? | throwError "no append law for {h}"
      let hf := mkAppN (mkConst law) F.getAppArgs
      let (p, L, _, z) := CertificateChecks.KernelCo2.Join.tree F hf sl 0 sl.size
      let jn := ns ++ Name.mkSimple s!"{pre}_join{i}"
      addThm jn (boolEq (mkApp2 (mkConst ``Nat.beq) (mkApp2 F L x0) z)) p
      pure (mkConst jn, L)
    let csN := ns ++ Name.mkSimple s!"{pre}_cs{i}"
    addDefn csN (mkApp (mkConst ``List [0]) (mkConst ``Nat)) L
    modify fun s => { s with σ := s.σ.insert csH (mkConst csN) }
    if Y.isMVar then modify fun s => { s with σ := s.σ.insert Y.mvarId!.name x }
    let lhs := mkApp2 F L x0
    return (mkApp2 (mkConst ``CFSG.KC.Th.Gen.eqN) lhs x,
      mkApp3 (mkConst ``CFSG.KC.Th.Gen.eqN_of) lhs x p)
  if !c.hasMVar then
    match ix.exact[c]? with
    | some p => return (c, p)
    | none =>
      if c.isAppOfArity ``CFSG.KC.Th.Gen.eqN 2 && c.getArg! 0 == c.getArg! 1 then
        let a := c.getArg! 0
        return (c, mkApp3 (mkConst ``CFSG.KC.Th.Gen.eqN_of) a a
          (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)))
      throwError "no check theorem for the conjunct{indentExpr c}"
  let σ := (← get).σ
  for (t, p) in ix.all do
    if let some σ' := matchE c t σ then
      modify fun s => { s with σ := σ' }
      return (t, p)
  throwError "no check theorem matches the conjunct{indentExpr c}"

end CertificateChecks.KernelTh.Assemble

open CertificateChecks.KernelTh.Assemble in
elab "#th_assemble " p:ident s:ident chk:ident : command => do
  let env ← getEnv
  let S ← liftCoreM <| realizeGlobalConstNoOverload s
  let chkN ← liftCoreM <| realizeGlobalConstNoOverload chk
  unless isStructure env S do throwError "{S} is not a structure"
  let ctor := getStructureCtor env S
  let fields := getStructureFields env S
  let some (.defnInfo ci) := env.find? chkN | throwError "{chkN} is not a definition"
  let .lam _ _ body _ := ci.value | throwError "{chkN}: expected `fun D => …`"
  let mut val : Std.HashMap Name Expr := {}
  for f in fields do
    let fs := f.toString
    if isFound fs then val := val.insert f (hole f)
    else match kdConst env fs with
      | .ok n => val := val.insert f (mkConst n)
      | .error e => throwError e
  let pat := normLits <| body.instantiate1 (mkFVar ⟨`_thAssembleD⟩)
  let pat := pat.replace fun x =>
    match x with
    | .app (.const pf _) (.fvar ⟨`_thAssembleD⟩) =>
      if pf.getPrefix == S then val[pf.componentsRev.head!]? else none
    | .proj _ i (.fvar ⟨`_thAssembleD⟩) => fields[i]? >>= (val[·]?)
    | _ => none
  if pat.hasLooseBVars || pat.hasFVar then throwError "{chkN}: the data occurs outside a field"
  let ix := buildIndex env
  let ns ← getCurrNamespace
  let pre := p.getId.toString
  let ((_, pf), st) ← (go ix pre ns pat).run {}
  let mut args : Array Expr := #[]
  for f in fields do
    let v := val[f]!
    if v.isMVar then
      match st.σ[v.mvarId!.name]? with
      | some e => args := args.push e
      | none => throwError "field {f} not found"
    else args := args.push v
  let dataN := ns ++ Name.mkSimple s!"{pre}Data"
  addDefn dataN (mkConst S) (mkAppN (mkConst ctor.name) args)
  addThm (ns ++ Name.mkSimple s!"{pre}_ok") (boolEq (mkApp (mkConst chkN) (mkConst dataN))) pf
