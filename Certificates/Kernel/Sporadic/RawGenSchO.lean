module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Data.Kernel.Spor.RawSch3G
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGenSchO

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit

meta def rflT : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

meta def origTab (k : Nat) : Nat :=
  (List.range k).foldl (fun acc j => acc ||| (j <<< (8 + 8 * j))) k

meta def soT (c : Ctx) (CH TS : Nat) (sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK)
    #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS,
      c.k `BP, lit c.nb, lit 0, lit TS, mulE sE (lit CH), lit CH])

meta def kOOf (P : Name) : CommandElabM Nat := do
  let hdA := (← getConstInfo (P ++ `head)).type.getAppArgs[1]!.getAppArgs
  match hdA[8]! with
  | .lit (.natVal k) => pure k
  | _ => throwError "{P}.head: the original generator count is not a literal"

meta def listTab (J : List Nat) : Nat :=
  (List.range J.length).foldl (fun acc k => acc ||| (J[k]! <<< (8 + 8 * k))) J.length

meta def addE (a b : Expr) : Expr :=
  mkAppN (mkConst ``HAdd.hAdd [0, 0, 0])
    #[natT, natT, natT, mkApp2 (mkConst ``instHAdd [0]) natT (mkConst ``instAddNat), a, b]

meta def lv12T (c : Ctx) (lE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lv12K)
    #[c.wE, c.mE, c.k `S, c.k `SI, lit c.kS, c.k `BP, lE, c.steps (addE lE (lit 1)),
      c.steps (addE (addE lE (lit 1)) (lit 1))])

end CFSG.KS.RawGenSchO

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchO in
elab "#ks_rawchain_sl2_osub " pre:ident js:num* wId:(ident)? : command => do
  let P := pre.getId
  let c ← ctxOf P
  unless 3 ≤ c.nb do throwError "#ks_rawchain_sl2_osub: {c.nb} levels, expected at least 3"
  let kO ← kOOf P
  let J := (js.map (·.getNat)).toList
  let TS := if J.isEmpty then origTab kO else listTab J
  let stAtE := fun (aE : Expr) => mkApp2 (mkConst ``CFSG.KS.Raw.stAt) (lit TS) aE
  let stCntE := mkApp (mkConst ``CFSG.KS.Raw.stCnt) (lit TS)
  unless J.all (· < kO) do throwError "#ks_rawchain_sl2_osub: the subset letters must be below {kO}"
  let wN? ← wId.mapM fun w => liftCoreM <| realizeGlobalConstNoOverload w
  if !J.isEmpty && wN?.isNone then throwError "#ks_rawchain_sl2_osub: a subset needs its words"
  withSync do
    addDef (P ++ `pTS) natT (lit TS)
    addRefl (P ++ `inv) (isTrue (mkApp2 (mkConst ``CFSG.KS.Raw.invTabK) (lit c.kS) (c.steps (lit 0))))
    for l in [0:c.nb - 2] do
      addRefl (P ++ Name.mkSimple s!"g{l + 1}{l + 2}") (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lv12K)
        #[c.wE, c.mE, c.k `S, c.k `SI, lit c.kS, c.k `BP, lit l, c.steps (lit (l + 1)),
          c.steps (lit (l + 2))]))
    addRefl (P ++ `tsb) (isTrue (mkApp2 (mkConst ``CFSG.KC.Enum.allN) stCntE
      (mkLambda `a .default natT (mkApp2 (mkConst ``Nat.blt) (stAtE (mkBVar 0)) (lit c.kS)))))
    match wN? with
    | none =>
      addRefl (P ++ `tso) (isTrue (mkApp2 (mkConst ``CFSG.KC.Enum.allN) (lit kO)
        (mkLambda `j .default natT (mkApp2 (mkConst ``CFSG.KS.Raw.anyLt) stCntE
          (mkLambda `a .default natT (mkApp2 (mkConst ``Nat.beq) (stAtE (mkBVar 0)) (mkBVar 1)))))))
    | some wN =>
      let TJ := listTab (J ++ J)
      addDef (P ++ `pTJ) natT (lit TJ)
      addDef (P ++ `oWS) (mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) natT)) (mkConst wN)
      addRefl (P ++ `owd) (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.wdsK)
        #[c.nE, c.wE, c.mE, c.idE, c.k `S, c.k `SI, lit kO, mkConst (P ++ `pTJ), c.k `oWS, lit 0]))
      addRefl (P ++ `oinc) (isTrue (mkApp2 (mkConst ``CFSG.KS.Raw.incK) (mkConst (P ++ `pTJ))
        (lit TS)))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchO in
elab "#ks_rawchain_sl2_scho " pre:ident lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let CH ← natOf (P ++ `pCH)
  let TS ← natOf (P ++ `pTS)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      addRefl (P ++ Name.mkSimple s!"so_{s}") (soT c CH TS (lit s))

end
