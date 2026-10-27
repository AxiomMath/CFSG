module

public import Certificates.Kernel.SporSch.Mathieu.GenBT
public import Certificates.Data.Kernel.SporSch.SylElts
public meta import Certificates.Kernel.SporSch.Mathieu.GenBT

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.MBTG

meta def parseElts (n : Nat) (s : String) :
    Except String (Array (Array Nat × Nat × Nat × Array Nat)) := do
  let mut out := #[]
  for ln in s.splitOn "\n" do
    let ws := (ln.splitOn " ").filter (· ≠ "")
    if ws.isEmpty then continue
    let vs ← ws.mapM fun t => match t.toNat? with
      | some v => pure v
      | none => throw s!"parseElts: bad token {t}"
    if vs.length != 2 * n + 2 then throw s!"parseElts: line of {vs.length} entries"
    out := out.push ((vs.take n).toArray, vs[n]!, vs[n + 1]!, (vs.drop (n + 2)).toArray)
  return out

end CFSG.KS.SporSch.MBTG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.MBTG in
elab "#kss_sylelts " pre:ident qq:ident nn:num ww:num nbN:num rl:ident moN:num hId:ident :
    command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let nb := nbN.getNat
  let mo := moN.getNat
  let RL ← liftCoreM <| realizeGlobalConstNoOverload rl
  let es ← match parseElts n (← evalStr hId) with
    | .ok r => pure r
    | .error e => throwError e
  let es := (es.map fun (x, o, j, c) => (pack w x, o, j, pack w c)).qsort (fun a b => a.1 < b.1)
  let len := es.size
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let getD := fun (l : Expr) (i : Expr) =>
    mkAppN (mkConst ``List.getD [0]) #[natT, l, i, lit 0]
  let XL := mkConst (P ++ `XL)
  let eltT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.MBT.eltK)
    #[nE, wE, mE, mulE nE wE, mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE, mkConst (Q ++ `LR),
      mkConst (Q ++ `TRI), mkConst (Q ++ `BP), lit nb, XL, mkConst RL, lit mo, getD XL iE,
      getD (mkConst (P ++ `OL)) iE, getD (mkConst (P ++ `JL)) iE, getD (mkConst (P ++ `CL)) iE])
  let ltE := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, a, b]
  withSync do
    addDef (P ++ `XL) listT (listE (es.map (·.1)).toList)
    addDef (P ++ `OL) listT (listE (es.map (·.2.1)).toList)
    addDef (P ++ `JL) listT (listE (es.map (·.2.2.1)).toList)
    addDef (P ++ `CL) listT (listE (es.map (·.2.2.2)).toList)
    addThm (P ++ `inc) (isTrue (mkApp2 (mkConst ``CFSG.KS.SporSch.MBT.incL) (lit 0) XL))
      reflBoolTrue
    for i in [0:len] do
      addThm (P ++ Name.mkSimple s!"e{i}") (eltT (lit i)) reflBoolTrue
    let hT := mkForall `i .default natT (mkForall `h .default (ltE (mkBVar 0) (lit len))
      (eltT (mkBVar 1)))
    let pE := mkLambda `i .default natT (eltT (mkBVar 0))
    let hV := forallChain pE len fun i => mkConst (P ++ Name.mkSimple s!"e{i}")
    addThm (P ++ `he) hT hV

end
