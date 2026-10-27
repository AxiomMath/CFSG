module

public import Certificates.Kernel.LocalComp.BlockGen
public meta import Lean

public section

namespace CFSG.KC.BlockGen

open Lean Meta Elab Tactic CFSG.KC.Tab CFSG.KS.RawGen

elab "lc_cover " bN:num : tactic => liftMetaFinishingTactic fun g => do
  let ty ← instantiateMVars (← g.getType)
  let .forallE tn tt (.forallE _ hlt body _) _ := ty
    | throwError "lc_cover: the goal is not `∀ t < n, F t = true`"
  unless hlt.isAppOfArity ``LT.lt 4 do throwError "lc_cover: the bound is not `t < n`"
  let some n := hlt.appArg!.rawNatLit? <|> hlt.appArg!.nat?
    | throwError "lc_cover: the bound is not a numeral"
  let some (_, lhs, _) := (body.lowerLooseBVars 1 1).eq?
    | throwError "lc_cover: the body is not `F t = true`"
  let B := bN.getNat
  unless 0 < B ∧ 0 < n do throwError "lc_cover: empty block or range"
  let f := Expr.lam tn tt lhs .default
  let nb := (n + B - 1) / B
  let gE := mkApp2 (mkConst ``CFSG.KC.Co3Bfs.guardF) (lit n) f
  let bodyT := fun (kE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KC.Co3Bfs.allFrom)
    #[mulE (lit B) kE, lit B, gE])
  let mut blocks := #[]
  for k in [0:nb] do
    blocks := blocks.push (← mkAuxLemma [] (bodyT (lit k)) reflBoolTrue (kind? := `blk) (cache := false))
  let PE := mkLambda `k .default natT (bodyT (mkBVar 0))
  let hall := forallChain PE nb fun k => mkConst blocks[k]!
  let hB := mkApp (mkConst ``Nat.zero_lt_succ) (lit (B - 1))
  let hn := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit n) (lit (B * nb)) reflBoolTrue
  g.assign (mkAppN (mkConst ``CFSG.KC.Co3Bfs.cover_of_blocks) #[f, lit n, lit B, lit nb, hB, hn, hall])

end CFSG.KC.BlockGen

end
