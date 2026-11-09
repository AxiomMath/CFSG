module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl
public import Certificates.Kernel.TwoHS.WKChain
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command Term Meta

namespace CFSG.KD.TwoHS.WKGen

meta def evalWord (wd : Syntax) : CommandElabM (List Nat) := do
  let listNat := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
  let word ← liftTermElabM do
    let e ← elabTerm wd (some listNat)
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unsafe evalExpr (List Nat) listNat e
  unless word.all (fun l => 1 ≤ l && l ≤ 6) do
    throwError "#kwk: the word has a letter outside 1, …, 6"
  return word

meta def gens : Array (Array Nat) :=
  (List.finRange 6).toArray.map fun i => (CFSG.EvenSporadicStandard.TwoHS.harY i).map (·.toNat)

end CFSG.KD.TwoHS.WKGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KD.TwoHS.WKGen in
elab "#kwk_val " pre:ident wd:term : command => do
  let P := (← getCurrNamespace) ++ pre.getId
  let word ← evalWord wd
  let gs := gens
  let mut cur : Array Nat := Array.range 11200
  for l in word do
    cur := comp 11200 cur gs[l - 1]!
  liftCoreM <| withOptions (Elab.async.set · false) <| addDef (P ++ `v) natT (lit (pack 14 cur))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KD.TwoHS.WKGen in
elab "#kwk_chain " pre:ident ss:num wd:term : command => do
  let Q := pre.getId
  let P := (← getCurrNamespace) ++ Q
  let s := ss.getNat
  let word ← evalWord wd
  let n := 11200
  let gens := gens
  let K := (word.length + s - 1) / s
  let mut cur : Array Nat := Array.range n
  let mut vals : Array Nat := #[pack 14 cur]
  for k in [0:K] do
    for l in (word.drop (s * k)).take s do
      cur := comp n cur gens[l - 1]!
    vals := vals.push (pack 14 cur)
  liftCoreM <| withOptions (Elab.async.set · false) <| addTree (P ++ `C) vals
  let cId := mkIdent (P ++ `C)
  let okId := mkIdent (Q ++ `ok)
  let okF := mkIdent (P ++ `ok)
  let idId := mkIdent (Q ++ `id)
  let allId := mkIdent (Q ++ `all)
  let vId := mkIdent (Q ++ `v)
  let eqId := mkIdent (Q ++ `eq)
  let sQ := Syntax.mkNumLit (toString s)
  let kQ := Syntax.mkNumLit (toString K)
  elabCommand (← `(command|
    @[expose] noncomputable def $okId (k : Nat) : Bool :=
      Nat.beq (CFSG.KS.MulH.wfoldK 11200 14 (CFSG.KS.mask 14) CFSG.KD.TwoHS.L
        ((($wd).drop ($sQ:num * k)).take $sQ:num) ($cId k)) ($cId (k + 1))))
  elabCommand (← `(command| #kc_each $okId 0 $kQ:num))
  elabCommand (← `(command|
    theorem $idId : Nat.beq ($cId 0) CFSG.KD.TwoHS.idK = true := by quickRfl))
  elabCommand (← `(command| #kc_forall_chunks $allId (fun k => $okId k = true) $kQ:num $okF 1))
  elabCommand (← `(command| @[expose] noncomputable def $vId : Nat := $cId $kQ:num))
  elabCommand (← `(command|
    theorem $eqId : CFSG.KD.TwoHS.WK ($wd) = $vId :=
      CFSG.KD.TwoHS.WK_chain (s := $sQ:num) (K := $kQ:num) (Nat.le_of_ble_eq_true (by quickRfl)) $idId $allId))

open Lean Elab Tactic Meta in
elab "bAnd_split" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := t.eq? | throwError "bAnd_split: the goal is not an equation"
  let args := lhs.getAppArgs
  unless lhs.isAppOfArity ``Bool.rec 4 do throwError "bAnd_split: the goal is not bAnd(a, b) = true"
  let b := args[2]!
  let a := args[3]!
  let ga ← mkFreshExprSyntheticOpaqueMVar (← mkEq a (mkConst ``Bool.true))
  let gb ← mkFreshExprSyntheticOpaqueMVar (← mkEq b (mkConst ``Bool.true))
  g.assign (mkApp4 (mkConst ``CFSG.KD.TwoHS.bAnd_true) a b ga gb)
  replaceMainGoal [ga.mvarId!, gb.mvarId!]
