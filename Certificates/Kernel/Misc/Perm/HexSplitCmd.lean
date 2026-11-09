module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
meta import all Lean.Shell
public import CFSG.Certificates.Kernel.Misc.HexFlatSplit
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KC.Misc.HexSplit

meta def addDeclDeep (mb : Nat) (x : CoreM Unit) : CoreM Unit := do
  let ctx ← read
  let s ← get
  Lean.Internal.setThreadStackSize (USize.ofNat (mb * 1024 * 1024))
  let t ← IO.asTask (prio := .dedicated) (x.toIO ctx s)
  let r ← IO.wait t
  Lean.Internal.setThreadStackSize (USize.ofNat (8 * 1024 * 1024))
  match r with
  | .ok ((), s') => set s'
  | .error e => throwError m!"{e}"

meta def hexVal (c : Nat) : Nat :=
  if c < 48 then 16 else if c < 58 then c - 48 else if c < 65 then 16 else if c < 71 then c - 55
  else 16

meta def states (d n w N m : Nat) (F : Array Nat) (cs : Array Char) :
    Except String (Array (Nat × Nat × Nat × Nat × Nat)) := do
  let mut st : Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 0)
  let mut out := #[st]
  for i in [0:cs.size] do
    if i > 0 && i % m == 0 then out := out.push st
    let (j, e, t, v, acc) := st
    if j == N then return out
    let h := hexVal cs[i]!.toNat
    if h ≥ 16 then throw s!"not a hex digit at {i}"
    let v' := v * 16 + h
    if t + 1 == d then
      if v' ≥ 2 ^ w then throw s!"value too large at {i}"
      let acc' := acc ||| (v' <<< (w * e))
      if e + 1 == n then
        if acc' != F[j]! then throw s!"entry {j} differs"
        st := (j + 1, 0, 0, 0, 0)
      else st := (j, e + 1, 0, 0, acc')
    else st := (j, e, t + 1, v', acc)
  return out

meta def statesT (wd n w m : Nat) (F : Array Nat) (cs : Array Char) :
    Except String (Array (Nat × Nat × Nat × Nat × Nat)) := do
  let mut st : Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 0)
  let mut out := #[st]
  for i in [0:cs.size] do
    if i > 0 && i % m == 0 then out := out.push st
    let (L, e, t, v, acc) := st
    let c := cs[i]!.toNat
    if e < n then
      let h := hexVal c
      if h ≥ 16 then throw s!"not a hex digit at {i}"
      let v' := v * 16 + h
      if t + 1 == wd then
        if v' ≥ 2 ^ w then throw s!"value too large at {i}"
        st := (L, e + 1, 0, 0, acc ||| (v' <<< (w * e)))
      else st := (L, e, t + 1, v', acc)
    else
      if c != 10 then throw s!"expected a newline at {i}"
      if L < F.size && acc != F[L]! then throw s!"line {L} differs"
      st := (L + 1, 0, 0, 0, 0)
  return out

end CFSG.KC.Misc.HexSplit

open CFSG.KC.Tab CFSG.KC.Misc.HexSplit in
elab "#kmisc_hexflat_split " pre:ident sId:ident dd:num nn:num ww:num cn:num mm:num : command => do
  let P := pre.getId
  let d := dd.getNat
  let n := nn.getNat
  let w := ww.getNat
  let N := cn.getNat
  let m := mm.getNat
  if m == 0 then throwError "#kmisc_hexflat_split: the piece length is 0"
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let b := s.toUTF8
  if b.size < d * n * N then throwError "#kmisc_hexflat_split: {b.size} bytes, expected {d * n * N}"
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let vals := Array.ofFn (n := N) fun j => Id.run do
    let mut acc := 0
    for i in [0:n] do
      let v := (List.range d).foldl (fun a t => a * 16 + hv (b.get! (d * (n * j.val + i) + t))) 0
      acc := acc ||| (v <<< (w * i))
    return acc
  let cs := s.toList.toArray
  let sts ← match states d n w N m vals cs with
    | .ok r => pure r
    | .error e => throwError "#kmisc_hexflat_split: {e}"
  let np := sts.size
  let charE : Expr := mkConst ``Char
  let lty := mkApp (mkConst ``List [0]) charE
  let consC := mkApp (mkConst ``List.cons [0]) charE
  let nilC := mkApp (mkConst ``List.nil [0]) charE
  let boolE := mkConst ``Bool
  let eqE := fun (ty a b : Expr) => mkApp3 (mkConst ``Eq [1]) ty a b
  let reflE := fun (ty a : Expr) => mkApp2 (mkConst ``Eq.refl [1]) ty a
  let trueE := mkConst ``Bool.true
  let isTrue := fun (x : Expr) => eqE boolE x trueE
  let FE := mkConst (P ++ `F)
  let hd := #[lit d, lit n, lit w, lit N, FE]
  let stE := fun (i : Nat) => let (j, e, t, v, a) := sts[i]!; #[lit j, lit e, lit t, lit v, lit a]
  let runE := fun (x : Expr) (st : Array Expr) =>
    mkAppN (mkConst ``CFSG.KC.Misc.HexFlat.run) (hd ++ #[x] ++ st)
  let sfN := fun (i : Nat) => P ++ Name.mkSimple s!"hsfx{i}"
  let pcN := fun (i : Nat) => P ++ Name.mkSimple s!"hpc{i}"
  let drN := fun (i : Nat) => P ++ Name.mkSimple s!"hdr{i}"
  let rnN := fun (i : Nat) => P ++ Name.mkSimple s!"hrn{i}"
  let thmV := fun (name : Name) (type value : Expr) =>
    CFSG.KC.addThmDecl ({ name := name, levelParams := [], type := type, value := value } : TheoremVal)
  let deep := fun (x : CoreM Unit) =>
    addDeclDeep 4096 <| withOptions (maxRecDepth.set · 100000000) x
  let env ← getEnv
  let viaSfx := env.contains (P ++ `chars_sfx)
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree (P ++ `F) vals
    let mut chE : Std.HashMap Nat Expr := {}
    for c in cs do
      unless chE.contains c.toNat do
        chE := chE.insert c.toNat (mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat))
    let mut acc := nilC
    let mut sfx : Array Expr := Array.replicate np nilC
    for i' in [0:cs.size] do
      let i := cs.size - 1 - i'
      acc := mkApp2 consC chE[cs[i]!.toNat]! acc
      if i % m == 0 && i / m < np then sfx := sfx.set! (i / m) acc
    for i in [0:np] do
      deep <| addDef (sfN i) lty sfx[i]!
    deep <| thmV (rnN (np - 1)) (isTrue (runE (mkConst (sfN (np - 1))) (stE (np - 1))))
      (reflE boolE trueE)
    for i' in [1:np] do
      let i := np - 1 - i'
      let pc := mkAppN (mkConst ``CFSG.KC.Misc.HexFlat.runTo)
        (hd ++ stE (i + 1) ++ #[lit m, mkConst (sfN i)] ++ stE i)
      deep <| thmV (pcN i) (isTrue pc) (reflE boolE trueE)
      let dr := mkApp2 (mkConst ``CFSG.KC.Misc.HexFlat.dropL) (lit m) (mkConst (sfN i))
      deep <| thmV (drN i) (eqE lty dr (mkConst (sfN (i + 1)))) (reflE lty (mkConst (sfN (i + 1))))
      let (J, E, T, V, A) := sts[i + 1]!
      let (j, e, t, v, a) := sts[i]!
      let pf := mkAppN (mkConst ``CFSG.KC.Misc.HexFlat.run_split')
        (hd ++ #[lit J, lit E, lit T, lit V, lit A, lit m, mkConst (sfN i), mkConst (sfN (i + 1)),
          lit j, lit e, lit t, lit v, lit a, mkConst (pcN i), mkConst (drN i), mkConst (rnN (i + 1))])
      thmV (rnN i) (isTrue (runE (mkConst (sfN i)) (stE i))) pf
    let z := #[lit 0, lit 0, lit 0, lit 0, lit 0]
    let charsE := mkConst (P ++ `chars)
    let r0 := mkConst (rnN 0)
    let r := if viaSfx then
        let motive := mkLambda `x .default lty (isTrue (runE (.bvar 0) z))
        let h := mkApp4 (mkConst ``Eq.symm [1]) lty charsE (mkConst (P ++ `sfx0))
          (mkConst (P ++ `chars_sfx))
        mkAppN (mkConst ``Eq.subst [0]) #[lty, motive, mkConst (P ++ `sfx0), charsE, h, r0]
      else r0
    let ty := isTrue (mkAppN (mkConst ``CFSG.KC.Misc.HexFlat.hexFlat)
      #[charsE, lit d, lit n, lit w, lit N, FE])
    let pf := mkAppN (mkConst ``CFSG.KC.Misc.HexFlat.hexFlat_of_run)
      #[charsE, lit d, lit n, lit w, lit N, FE, reflE boolE trueE, reflE boolE trueE, r]
    thmV (P ++ `all) ty pf

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.Misc.HexSplit in
elab "#ks_hexlines_split " pre:ident sId:ident wdN:num nN:num wN:num mm:num : command => do
  let P := pre.getId
  let wd := wdN.getNat
  let n := nN.getNat
  let w := wN.getNat
  let m := mm.getNat
  if m == 0 then throwError "#ks_hexlines_split: the piece length is 0"
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let hexv := fun (c : Char) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let ls := (s.splitOn "\n").filter (· ≠ "")
  let vals := ls.toArray.map fun l =>
    let cs := l.toList.toArray
    pack w (Array.ofFn (n := n) fun i => (List.range wd).foldl (fun acc t => acc * 16 +
      hexv cs[wd * i.val + t]!) 0)
  let cs := s.toList.toArray
  let sts ← match statesT wd n w m vals cs with
    | .ok r => pure r
    | .error e => throwError "#ks_hexlines_split: {e}"
  let np := sts.size
  let lines := vals.size
  let charE : Expr := mkConst ``Char
  let lty := mkApp (mkConst ``List [0]) charE
  let consC := mkApp (mkConst ``List.cons [0]) charE
  let nilC := mkApp (mkConst ``List.nil [0]) charE
  let boolE := mkConst ``Bool
  let eqE := fun (ty a b : Expr) => mkApp3 (mkConst ``Eq [1]) ty a b
  let reflE := fun (ty a : Expr) => mkApp2 (mkConst ``Eq.refl [1]) ty a
  let trueE := mkConst ``Bool.true
  let isT := fun (x : Expr) => eqE boolE x trueE
  let FE := mkConst (P ++ `L)
  let hd := #[lit wd, lit n, lit w, lit lines, lit 0, lit lines, FE]
  let stE := fun (i : Nat) => let (j, e, t, v, a) := sts[i]!; #[lit j, lit e, lit t, lit v, lit a]
  let runE := fun (x : Expr) (st : Array Expr) => mkAppN (mkConst ``CFSG.KS.Text.run) (hd ++ #[x] ++ st)
  let sfN := fun (i : Nat) => P ++ Name.mkSimple s!"hsfx{i}"
  let pcN := fun (i : Nat) => P ++ Name.mkSimple s!"hpc{i}"
  let drN := fun (i : Nat) => P ++ Name.mkSimple s!"hdr{i}"
  let rnN := fun (i : Nat) => P ++ Name.mkSimple s!"hrn{i}"
  let thmV := fun (name : Name) (type value : Expr) =>
    CFSG.KC.addThmDecl ({ name := name, levelParams := [], type := type, value := value } : TheoremVal)
  let deep := fun (x : CoreM Unit) =>
    addDeclDeep 4096 <| withOptions (maxRecDepth.set · 100000000) x
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `L) vals
    addDef (P ++ `lines) natT (lit lines)
    let mut chE : Std.HashMap Nat Expr := {}
    for c in cs do
      unless chE.contains c.toNat do
        chE := chE.insert c.toNat (mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat))
    let mut acc := nilC
    let mut sfx : Array Expr := Array.replicate np nilC
    for i' in [0:cs.size] do
      let i := cs.size - 1 - i'
      acc := mkApp2 consC chE[cs[i]!.toNat]! acc
      if i % m == 0 && i / m < np then sfx := sfx.set! (i / m) acc
    for i in [0:np] do
      deep <| addDef (sfN i) lty sfx[i]!
    deep <| thmV (rnN (np - 1)) (isT (runE (mkConst (sfN (np - 1))) (stE (np - 1)))) (reflE boolE trueE)
    for i' in [1:np] do
      let i := np - 1 - i'
      let pc := mkAppN (mkConst ``CFSG.KS.Text.runTo)
        (hd ++ stE (i + 1) ++ #[lit m, mkConst (sfN i)] ++ stE i)
      deep <| thmV (pcN i) (isT pc) (reflE boolE trueE)
      let dr := mkApp2 (mkConst ``CFSG.KC.Misc.HexFlat.dropL) (lit m) (mkConst (sfN i))
      deep <| thmV (drN i) (eqE lty dr (mkConst (sfN (i + 1)))) (reflE lty (mkConst (sfN (i + 1))))
      let pf := mkAppN (mkConst ``CFSG.KS.Text.run_split')
        (hd ++ stE (i + 1) ++ #[lit m, mkConst (sfN i), mkConst (sfN (i + 1))] ++ stE i ++
          #[mkConst (pcN i), mkConst (drN i), mkConst (rnN (i + 1))])
      thmV (rnN i) (isT (runE (mkConst (sfN i)) (stE i))) pf
    let charsE := mkConst (P ++ `chars)
    let ty := isT (mkAppN (mkConst ``CFSG.KS.Text.hexBind)
      #[charsE, lit wd, lit n, lit w, lit lines, lit 0, lit lines, FE])
    let pf := mkAppN (mkConst ``CFSG.KS.Text.hexBind_of_run)
      #[charsE, lit wd, lit n, lit w, lit lines, lit 0, lit lines, FE, reflE boolE trueE,
        reflE boolE trueE, mkConst (rnN 0)]
    thmV (P ++ `all) ty pf
