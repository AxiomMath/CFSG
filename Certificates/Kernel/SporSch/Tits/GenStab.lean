module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KS.GenStab

open CFSG.KS.RawGen

public meta def wv (n : Nat) (S Si : Array (Array Nat)) (wd : List Int) : Array Nat :=
  wd.foldr (fun (l : Int) acc =>
    comp n (if 0 < l then S[l.toNat - 1]! else Si[(-l).toNat - 1]!) acc) (Array.range n)

public meta def bfs (n : Nat) (gens : Array (Array Nat)) (r : Nat) :
    Array Nat × Array Nat × Array Nat :=
  Id.run do
    let mut seen := (Array.replicate n false).set! r true
    let mut dep := Array.replicate n 0
    let mut par := Array.replicate n 0
    let mut gl := Array.replicate n 0
    let mut q : Array Nat := #[r]
    let mut h := 0
    while h < q.size do
      let x := q[h]!
      h := h + 1
      for i in [0:gens.size] do
        let y := gens[i]![x]!
        if !seen[y]! then
          seen := seen.set! y true
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          gl := gl.set! y i
          q := q.push y
    return (dep, par, gl)

public meta def unpackN (n w P : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => (P >>> (w * i.val)) % (1 <<< w)

public meta def litOf (c : Name) : CoreM Nat := do
  match ((← getEnv).find? c).bind ConstantInfo.value? with
  | some (.lit (.natVal v)) => pure v
  | _ => throwError "#kst_stab: {c} is not a literal"

end CFSG.KS.GenStab

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.GenStab in
elab "#kst_stab " pre:ident nn:num ww:num fId:ident wId:ident cId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let mut G : Array (Array Nat) := #[]
  for k in [0:4] do
    G := G.push (unpackN n w (← liftCoreM <| litOf (fN ++ Name.mkSimple s!"L{k}")))
  let W ← liftTermElabM <| unsafe evalConst (List (List Int)) wN
  let C ← liftTermElabM <| unsafe evalConst (List (List Int × List Int)) cN
  let Gi := G.map (inv n)
  let U := (C.toArray.extract 0 2).map fun c => wv n G Gi c.1
  let V := (C.toArray.extract 0 2).map fun c => wv n G Gi c.2
  let UI := U.map (inv n)
  let VI := V.map (inv n)
  let A := (List.range 2).toArray.map fun j => comp n UI[j]! VI[j]!
  let B := (List.range 2).toArray.map fun j => comp n A[j]! U[j]!
  let D := (List.range 2).toArray.map fun j => comp n B[j]! V[j]!
  let T := W.foldl (fun S wd => S.push (wv n S (S.map (inv n)) wd)) D
  let (dep, par, gl) := bfs n D 0
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `GI) (Gi.map (pack w))
    addTree (P ++ `U) (U.map (pack w))
    addTree (P ++ `UI) (UI.map (pack w))
    addTree (P ++ `V) (V.map (pack w))
    addTree (P ++ `VI) (VI.map (pack w))
    addTree (P ++ `A) (A.map (pack w))
    addTree (P ++ `B) (B.map (pack w))
    addTree (P ++ `T) (T.map (pack w))
    addTree (P ++ `TI) ((T.map (inv n)).map (pack w))
    addDef (P ++ `DEP) natT (lit (pack w dep))
    addDef (P ++ `PAR) natT (lit (pack w par))
    addDef (P ++ `GL) natT (lit (pack w gl))
