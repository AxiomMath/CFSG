module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Sporadic.Schreier.PairText
public import Certificates.Data.Kernel.SporSch.PairSyl
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.Sporadic.Schreier.PairText in
elab "#kss_sylp " pre:ident cId:ident wN:num : command => do
  let P := pre.getId
  let w := wN.getNat
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let R ← liftTermElabM <| unsafe evalConst (Array SylowRec) cN
  let natE := natT
  let intE := mkConst ``Int
  let lstT := fun (t : Expr) => mkApp (mkConst ``List [0]) t
  let mkL := fun (t : Expr) (xs : List Expr) =>
    xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) t x acc) (mkApp (mkConst ``List.nil [0]) t)
  let intL := fun (z : Int) => match z with
    | .ofNat k => mkApp (mkConst ``Int.ofNat) (lit k)
    | .negSucc k => mkApp (mkConst ``Int.negSucc) (lit k)
  let wordE := fun (l : List Int) => mkL intE (l.map intL)
  let wordsE := fun (ws : Array (List Int)) => mkL (lstT intE) (ws.toList.map wordE)
  let permsE := fun (ps : Array (Array Nat)) => mkL natE (ps.toList.map fun a => lit (pack w a))
  let chainE := fun (c : ChainRec) => mkAppN (mkConst ``CFSG.KS.SporSch.ChainP.mk)
    #[permsE c.gens, mkL natE (c.base.map lit), permsE c.strong, wordsE c.words]
  let recE := fun (r : NGRec) => mkAppN (mkConst ``CFSG.KS.SporSch.RecP.mk)
    #[lit (pack w r.rep), wordsE r.conj, chainE r.chain]
  let sylE := fun (s : SylowRec) => mkAppN (mkConst ``CFSG.KS.SporSch.SylP.mk)
    #[lit s.prime, permsE s.gens, mkL (mkConst ``CFSG.KS.SporSch.RecP) (s.records.toList.map recE)]
  let val := mkL (mkConst ``CFSG.KS.SporSch.SylP) (R.toList.map sylE)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `R) (lstT (mkConst ``CFSG.KS.SporSch.SylP)) val

end
