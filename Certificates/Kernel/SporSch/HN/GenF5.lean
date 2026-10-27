module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.SporSch.HNF5
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KS.SporSchGenF5

open CFSG.KC.Tab

meta def forallLt (k : Nat) (body : Expr → Expr) : Expr :=
  mkForall `q .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, mkNatLit k])
    (body (mkBVar 1)))

meta def mul5 (X Y : Array (Array Nat)) : Array (Array Nat) :=
  X.map fun x => (Array.range 133).map fun c =>
    ((Array.range 133).foldl (fun acc j => acc + x[j]! * (Y[j]!)[c]!) 0) % 5

meta def pack16 (r : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for j in [0:r.size] do
    acc := acc ||| (r[j]! <<< (16 * j))
  return acc

end CFSG.KS.SporSchGenF5

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGenF5 in
elab "#kss_f5table " pre:ident aId:ident bId:ident sId:ident : command => do
  let P := pre.getId
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let B ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) bN
  let spec ← liftTermElabM <| unsafe evalConst (List (Nat × Nat × Nat)) sN
  let mut M : Array (Array (Array Nat)) := #[A, B]
  for (op, l, r) in spec do
    M := M.push (if op == 0 then mul5 M[l]! M[r]! else M[l]!)
  let nE := M.size
  let rows := M.foldl (fun acc m => acc ++ m.map pack16) #[]
  let ops := #[1, 1] ++ (spec.map fun (op, _, _) => op).toArray
  let ls := #[0, 1] ++ (spec.map fun (_, l, _) => l).toArray
  let rs := #[0, 0] ++ (spec.map fun (_, _, r) => r).toArray
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `MT) rows
    addTree (P ++ `OP) ops
    addTree (P ++ `L) ls
    addTree (P ++ `R) rs
    addDef (P ++ `nE) natT (lit nE)
    let c := fun (s : Name) => mkConst (P ++ s)
    let ty := fun (k b : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.entryOK)
      #[c `MT, c `OP, c `L, c `R, mkApp2 (mkConst ``Nat.add) k (mkNatLit 2), b])
    for k in [0:nE - 2] do
      for b in [0:7] do
        let nm := P ++ Name.mkSimple ("e" ++ toString k ++ "_" ++ toString b)
        let tyb := ty (mkNatLit k) (mkNatLit b)
        CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyb, value := reflBoolTrue }
      let lamB := mkLambda `b .default natT (ty (mkNatLit k) (mkBVar 0))
      let vB := forallChain lamB 7 fun b => mkConst (P ++ Name.mkSimple ("e" ++ toString k ++ "_" ++ toString b))
      let tyB := forallLt 7 fun b => ty (mkNatLit k) b
      let nmk := P ++ Name.mkSimple ("e" ++ toString k)
      CFSG.KC.addThmDecl <| { name := nmk, levelParams := [], type := tyB, value := vB }
    let lamK := mkLambda `k .default natT (forallLt 7 fun b => ty (mkBVar 2) b)
    let vK := forallChain lamK (nE - 2) fun k => mkConst (P ++ Name.mkSimple ("e" ++ toString k))
    let tyK := forallLt (nE - 2) fun k => forallLt 7 fun b => ty (k.liftLooseBVars 0 2) b
    let nmAll := P ++ `hall
    CFSG.KC.addThmDecl <| { name := nmAll, levelParams := [], type := tyK, value := vK }

end
