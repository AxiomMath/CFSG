module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.SporSch.HN.GenF5
public import Certificates.Data.Kernel.SporSch.HNF5Mod
public import Certificates.Kernel.SporSch.HN.GenF5

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGenF5 in
elab "#kss_f5list " pre:ident mId:ident sId:ident : command => do
  let P := pre.getId
  let mN ← liftCoreM <| realizeGlobalConstNoOverload mId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let M ← liftTermElabM <| unsafe evalConst (List (Array (Array Nat))) mN
  let spec ← liftTermElabM <| unsafe evalConst (List (Nat × Nat × Nat)) sN
  let nE := M.length
  let rows := M.foldl (fun acc m => acc ++ m.map pack16) #[]
  let ops := (spec.map fun (op, _, _) => op).toArray
  let ls := (spec.map fun (_, l, _) => l).toArray
  let rs := (spec.map fun (_, _, r) => r).toArray
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `MT) rows
    addTree (P ++ `OP) ops
    addTree (P ++ `L) ls
    addTree (P ++ `R) rs
    addDef (P ++ `nE) natT (lit nE)
    let c := fun (s : Name) => mkConst (P ++ s)
    let ty := fun (k b : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.entryOK2)
      #[c `MT, c `OP, c `L, c `R, k, b])
    for k in [0:nE] do
      for b in [0:7] do
        let nm := P ++ Name.mkSimple ("e" ++ toString k ++ "_" ++ toString b)
        let tyb := ty (mkNatLit k) (mkNatLit b)
        CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyb, value := reflBoolTrue }
      let lamB := mkLambda `b .default natT (ty (mkNatLit k) (mkBVar 0))
      let vB := forallChain lamB 7 fun b =>
        mkConst (P ++ Name.mkSimple ("e" ++ toString k ++ "_" ++ toString b))
      let tyB := forallLt 7 fun b => ty (mkNatLit k) b
      let nmk := P ++ Name.mkSimple ("e" ++ toString k)
      CFSG.KC.addThmDecl <| { name := nmk, levelParams := [], type := tyB, value := vB }
    let lamK := mkLambda `k .default natT (forallLt 7 fun b => ty (mkBVar 2) b)
    let vK := forallChain lamK nE fun k => mkConst (P ++ Name.mkSimple ("e" ++ toString k))
    let tyK := forallLt nE fun k => forallLt 7 fun b => ty (k.liftLooseBVars 0 2) b
    CFSG.KC.addThmDecl <| { name := P ++ `hall, levelParams := [], type := tyK, value := vK }
