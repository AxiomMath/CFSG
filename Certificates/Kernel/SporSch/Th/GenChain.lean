module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.Th.Core
public import Certificates.Data.Kernel.SporSch.ThRows
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KS.SporSchGenChain

open CFSG.KC.Tab

meta def forallLt (k : Nat) (body : Expr → Expr) : Expr :=
  mkForall `q .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit k])
    (body (mkBVar 1)))

meta def v4n (v : CFSG.Sporadic.Th.Native.V4) : Nat :=
  v.w0.toNat ||| (v.w1.toNat <<< 64) ||| (v.w2.toNat <<< 128) ||| (v.w3.toNat <<< 192)

meta def vm (Y : Array Nat) (x : Nat) : Nat := Id.run do
  let mut acc := 0
  for j in [0:248] do
    if (x >>> j) &&& 1 == 1 then acc := acc ^^^ Y[j]!
  return acc

end CFSG.KS.SporSchGenChain

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGenChain in
elab "#kss_suffix " pre:ident aT:ident bbT:ident aId:ident bbId:ident wId:ident : command => do
  let P := pre.getId
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let bbN ← liftCoreM <| realizeGlobalConstNoOverload bbId
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let aTN ← liftCoreM <| realizeGlobalConstNoOverload aT
  let bbTN ← liftCoreM <| realizeGlobalConstNoOverload bbT
  let A ← liftTermElabM <| unsafe evalConst (Array CFSG.Sporadic.Th.Native.V4) aN
  let BB ← liftTermElabM <| unsafe evalConst (Array CFSG.Sporadic.Th.Native.V4) bbN
  let w ← liftTermElabM <| unsafe evalConst (List Int) wN
  let An := A.map v4n
  let BBn := BB.map v4n
  let n := w.length
  let lets := w.toArray.map fun l => if l == -1 then An else BBn
  let mut S : Array (Array Nat) := Array.replicate n #[]
  S := S.set! (n - 1) lets[n - 1]!
  for t in [0:n - 1] do
    let k := n - 2 - t
    S := S.set! k ((lets[k]!).map fun x => vm S[k + 1]! x)
  let ss := S.foldl (· ++ ·) #[]
  let lc := w.toArray.map fun l => if l == -1 then 0 else 1
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `SS) ss
    addTree (P ++ `LC) lc
    addDef (P ++ `n) natT (lit n)
    let SSc := mkConst (P ++ `SS)
    let let_ := fun (k : Expr) => mkAppN (mkConst ``CFSG.KS.SporSch.letRow)
      #[mkConst (P ++ `LC), mkConst aTN, mkConst bbTN, k]
    let sl := fun (k : Expr) => mkApp2 (mkConst ``CFSG.KS.SporSch.slice) SSc k
    let ty := fun (k b : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.mulBlkK)
      #[let_ k, sl (mkApp (mkConst ``Nat.succ) k), sl k,
        mkApp2 (mkConst ``Nat.mul) (lit 31) b, lit 31])
    let m := n - 1
    for k in [0:m] do
      for b in [0:8] do
        let nm := P ++ Name.mkSimple ("c" ++ toString k ++ "_" ++ toString b)
        let tyk := ty (lit k) (lit b)
        CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyk, value := reflBoolTrue }
      let lamB := mkLambda `b .default natT (ty (lit k) (mkBVar 0))
      let vB := forallChain lamB 8 fun b => mkConst (P ++ Name.mkSimple ("c" ++ toString k ++ "_" ++ toString b))
      let tyB := forallLt 8 fun b => ty (lit k) b
      let nmk := P ++ Name.mkSimple ("c" ++ toString k)
      CFSG.KC.addThmDecl <| { name := nmk, levelParams := [], type := tyB, value := vB }
    let lamK := mkLambda `k .default natT (forallLt 8 fun b => ty (mkBVar 2) b)
    let vK := forallChain lamK m fun k => mkConst (P ++ Name.mkSimple ("c" ++ toString k))
    let tyK := forallLt m fun k => forallLt 8 fun b => ty (k.liftLooseBVars 0 2) b
    let nmAll := P ++ `hc
    CFSG.KC.addThmDecl <| { name := nmAll, levelParams := [], type := tyK, value := vK }

end
