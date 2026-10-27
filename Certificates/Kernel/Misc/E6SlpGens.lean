module

public meta import Certificates.Kernel.StdOdd.SlpCmd
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.StdOdd.SlpCmd

public section

namespace CFSG.KC.Misc.E6Std

meta def blowT (P : Array (Nat × Nat)) : Nat := Id.run do
  let mut acc := 0
  for i' in [0:156] do
    let i := 155 - i'
    let k := i / 2
    let a := i % 2
    let mut row := 0
    for l in [0:78] do
      let v := P.getD l (0, 0)
      let x₀ := v.1.testBit k
      let x₁ := v.2.testBit k
      let e₀ := if a == 0 then x₀ else x₁
      let e₁ := if a == 0 then x₁ else x₀ ^^ x₁
      if e₀ then row := row ||| (1 <<< (2 * l))
      if e₁ then row := row ||| (1 <<< (2 * l + 1))
    acc := (acc <<< 156) ||| row
  return acc

open Lean Elab Command CFSG.KC.Tab

elab "#e6_slp_gens " pre:ident progId:ident gensId:ident : command => do
  let P := (← getCurrNamespace) ++ pre.getId
  let progN ← liftCoreM <| realizeGlobalConstNoOverload progId
  let gensN ← liftCoreM <| realizeGlobalConstNoOverload gensId
  let prog ← liftTermElabM <| unsafe evalConst (List (List Nat)) progN
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array (Nat × Nat))) gensN
  let n := gens.size
  let V := runT (gens.map blowT) prog
  let lnT := mkApp (mkConst ``List [0]) natT
  let e := V.toList.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)
  let progE := mkConst progN
  let VE := mkConst (P ++ `V)
  let line (t : Expr) : Expr :=
    mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp4 (mkConst ``slpLine) VE progE (lit n) t) (mkConst ``Bool.true)
  let motive := mkLambda `t .default natT (line (mkBVar 0))
  withSync do
    addDef (P ++ `V) lnT e
    let mut pf := mkApp (mkConst ``forall_lt_zero) motive
    for t in [0:prog.length] do
      let nm := P ++ Name.mkSimple s!"l{t}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := line (lit t), value := reflBoolTrue }
      pf := mkApp4 (mkConst ``forall_lt_succ) motive (lit t) pf (mkConst nm)
    let lt (x y : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) natT (mkConst ``instLTNat) x y
    let ty := mkForall `t .default natT (mkForall `h .default
      (lt (mkBVar 0) (mkApp (mkConst ``lenLL) progE)) (line (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `lines, levelParams := [], type := ty, value := pf }

end CFSG.KC.Misc.E6Std

end
