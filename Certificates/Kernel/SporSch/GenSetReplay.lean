module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Std.Data.HashMap
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.SporSch.SetReplay
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KS.SporSchGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def app (c : Name) (args : Array Expr) : Expr := mkAppN (mkConst c) args

meta def forallLt (k : Nat) (body : Expr → Expr) : Expr :=
  mkForall `q .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit k])
    (body (mkBVar 1)))

meta def addChain (P : Name) (nm allNm : String) (k : Nat) (ty : Expr → Expr) : CoreM Unit := do
  for q in [0:k] do
    let nmq := P ++ Name.mkSimple (nm ++ toString q)
    CFSG.KC.addThmDecl <| { name := nmq, levelParams := [], type := ty (lit q), value := reflBoolTrue }
  let lam := mkLambda `q .default natT (ty (mkBVar 0))
  let v := forallChain lam k fun q => mkConst (P ++ Name.mkSimple (nm ++ toString q))
  let nmAll := P ++ Name.mkSimple allNm
  let tyAll := forallLt k ty
  CFSG.KC.addThmDecl <| { name := nmAll, levelParams := [], type := tyAll, value := v }

meta def idxE (g : Expr) (R : Nat) (r : Expr) : Expr :=
  mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.mul) g (lit R)) r

meta def addChain2 (P : Name) (nm allNm : String) (nG R : Nat) (ty : Expr → Expr) :
    CoreM Unit := do
  for g in [0:nG] do
    for r in [0:R] do
      let nmq := P ++ Name.mkSimple s!"{nm}_{g}_{r}"
      let tyq := ty (idxE (lit g) R (lit r))
      CFSG.KC.addThmDecl <| { name := nmq, levelParams := [], type := tyq, value := reflBoolTrue }
    let lamR := mkLambda `r .default natT (ty (idxE (lit g) R (mkBVar 0)))
    let vR := forallChain lamR R fun r => mkConst (P ++ Name.mkSimple s!"{nm}_{g}_{r}")
    let tyR := forallLt R fun r => ty (idxE (lit g) R r)
    let nmg := P ++ Name.mkSimple s!"{nm}_{g}"
    CFSG.KC.addThmDecl <| { name := nmg, levelParams := [], type := tyR, value := vR }
  let lamG := mkLambda `g .default natT (forallLt R fun r => ty (idxE (mkBVar 2) R r))
  let vG := forallChain lamG nG fun g => mkConst (P ++ Name.mkSimple s!"{nm}_{g}")
  let tyG := forallLt nG fun g => forallLt R fun r => ty (idxE (g.liftLooseBVars 0 2) R r)
  let nmAll := P ++ Name.mkSimple allNm
  CFSG.KC.addThmDecl <| { name := nmAll, levelParams := [], type := tyG, value := vG }

meta def rows (rw : Nat) (vs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut i := 0
  while i < vs.size do
    let mut acc := 0
    for j in [0:64] do
      if i + j < vs.size then
        acc := acc ||| (vs[i + j]! <<< (rw * j))
    out := out.push acc
    i := i + 64
  return out

end CFSG.KS.SporSchGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kss_setreplay " pre:ident nn:num ww:num gId:ident sId:ident bb:num hh:num bk:num rr:num :
    command => do
  let P := pre.getId
  let R := rr.getNat
  let n := nn.getNat
  let w := ww.getNat
  let bound := bb.getNat
  let H := hh.getNat
  let B := bk.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let start ← liftTermElabM <| unsafe evalConst (List Nat) sN
  let kg := gens.size
  let s := start.length
  let key := fun (l : Array Nat) => l.foldl (fun acc p => acc ||| (1 <<< p)) 0
  let mut sets : Array (Array Nat) := #[start.toArray]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (key start.toArray) 0
  let mut wit : Array Nat := #[]
  let mut curAt : Array Nat := #[]
  let mut head := 0
  for _ in [0:bound] do
    if head < sets.size && sets.size < bound then
      curAt := curAt.push sets.size
      let st := sets[head]!
      let mut wv := 0
      for k in [0:kg] do
        if sets.size < bound then
          let t := (st.map fun p => (gens[k]!)[p]!).qsort (· < ·)
          let kt := key t
          match seen.get? kt with
          | some j => wv := wv ||| (j <<< (20 * k))
          | none =>
            wv := wv ||| (sets.size <<< (20 * k))
            seen := seen.insert kt sets.size
            sets := sets.push t
            par := par.push head
            lab := lab.push k
      wit := wit.push wv
      head := head + 1
  let c := sets.size
  let nS := (c + H * R - 1) / (H * R)
  let nB := (c + B * R - 1) / (B * R)
  let C := (Array.range (nS * R + 1)).map fun q => if q * H < curAt.size then curAt[q * H]! else c
  let sw := s * w
  let rx := sw + 28
  let xs := (Array.range c).map fun i => pack w sets[i]! ||| (par[i]! <<< sw) ||| (lab[i]! <<< (sw + 20))
  let kkey := fun (l : Array Nat) =>
    (l.foldl (fun acc p => acc + (p + 1) * 11400714819323198485) 0 % 2 ^ 64) ||| (key l <<< 64)
  let keys := sets.map kkey
  let so := (Array.range c).qsort fun a b => keys[a]! < keys[b]!
  let soi := Id.run do
    let mut r := Array.replicate c 0
    for i in [0:c] do
      r := r.set! so[i]! i
    return r
  let rwW := 20 * kg
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addTree (P ++ `GI) (gens.map fun g => pack w (inv n g))
    addTree (P ++ `XT) (rows rx xs)
    addTree (P ++ `WT) (rows rwW wit)
    addTree (P ++ `ST) (rows 20 so)
    addTree (P ++ `SIT) (rows 20 soi)
    addTree (P ++ `C) C
    addDef (P ++ `c) natT (lit c)
    addDef (P ++ `nS) natT (lit nS)
    addDef (P ++ `nB) natT (lit nB)
    addDef (P ++ `rx) natT (lit rx)
    let rg := fun (T : Name) (rw : Nat) => app ``CFSG.KS.SporSch.rowGet #[mkConst (P ++ T), lit rw]
    let X := rg `XT rx
    let W := rg `WT rwW
    let SO := rg `ST 20
    let SOI := rg `SIT 20
    let Cf := mkConst (P ++ `C)
    let runT := fun (q : Expr) => isTrue (mkApp2 (mkConst ``Nat.beq)
      (app ``CFSG.KS.SporSch.runFrom #[lit w, lit s, mkConst (P ++ `G), X, W, lit kg, lit c,
        lit bound, lit H, mkApp2 (mkConst ``Nat.mul) q (lit H), mkApp Cf q])
      (mkApp Cf (mkApp (mkConst ``Nat.succ) q)))
    addChain2 P "run" "hrun" nS R runT
    let eltT := fun (q : Expr) => isTrue (app ``CFSG.KC.Enum.allBlk
      #[mkApp2 (mkConst ``Nat.mul) q (lit B), app ``CFSG.KS.SporSch.eltAt #[lit n, lit w, lit s, X, lit c],
        lit B])
    addChain2 P "elt" "helt" nB R eltT
    let srtT := fun (q : Expr) => isTrue (app ``CFSG.KC.Enum.allBlk
      #[mkApp2 (mkConst ``Nat.mul) q (lit B), app ``CFSG.KS.SporSch.sortAt #[lit w, lit s, X, SO, SOI, lit c],
        lit B])
    addChain2 P "srt" "hsrt" nB R srtT

end
