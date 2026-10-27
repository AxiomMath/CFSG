module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Lean
public import Lean.Exception

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kst_surv " pre:ident ww:num lId:ident xId:ident : command => do
  let P := pre.getId
  let w := ww.getNat
  let lN ← liftCoreM <| realizeGlobalConstNoOverload lId
  let xN ← liftCoreM <| realizeGlobalConstNoOverload xId
  let Ls ← liftTermElabM <| unsafe evalConst (Array CFSG.Monster.B.Co2.Native.Level) lN
  let Xs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) xN
  let n := (Ls[0]!.tr[0]!).size
  let c := (List.range 5).map fun i => Ls[i]!.pts.size
  let mut tbl : Std.HashMap Nat Nat := {}
  for a in [0:c[0]!] do
    for b in [0:c[1]!] do
      let tab := comp n Ls[0]!.tr[a]! Ls[1]!.tr[b]!
      for cc in [0:c[2]!] do
        let tabc := comp n tab Ls[2]!.tr[cc]!
        for d in [0:c[3]!] do
          let t3 := comp n tabc Ls[3]!.tr[d]!
          for e in [0:c[4]!] do
            let g := comp n t3 Ls[4]!.tr[e]!
            let code := (((a * c[1]! + b) * c[2]! + cc) * c[3]! + d) * c[4]! + e
            tbl := tbl.insert (pack w g) code
  let Lv := Xs.map (pack w)
  let Cv ← Lv.mapM fun x => match tbl.get? x with
    | some k => pure k
    | none => throwError "#kst_surv: a listed array is not a product of the transversals"
  let M := Cv.foldl (fun m k => m ||| (1 <<< k)) 0
  let listE := fun (xs : List Nat) => xs.foldr (fun x acc =>
    mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc) (mkApp (mkConst ``List.nil [0]) natT)
  let ltyE := mkApp (mkConst ``List [0]) natT
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `L) ltyE (listE Lv)
    addDef (P ++ `C) ltyE (listE Cv)
    addDef (P ++ `M) natT (lit M)
