module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Co1.GenVOrb
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.SporSch.Co1Full
public import Certificates.Kernel.SporSch.Co1.GenVOrb

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.GenVOrb in
elab "#kss_co1fib " pre:ident tId:ident sId:ident pId:ident wN:num lN:num : command => do
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let tN ← get tId
  let sN ← get sId
  let pts ← liftTermElabM <| unsafe evalConst (Array Nat) (← get pId)
  let w := wN.getNat
  let L := lN.getNat
  let P := pre.getId
  let n := pts.size
  let set : Std.HashSet Nat := pts.foldl (fun s v => s.insert v) {}
  let NS := (n + L - 1) / L
  let mut cs : Array Nat := #[0]
  let mut cnt := 0
  for k in [0:NS * L] do
    if k < n && set.contains (pts[k]! ^^^ w) then cnt := cnt + 1
    if (k + 1) % L == 0 then cs := cs.push cnt
  let total := cnt
  let c := fun (s : Name) => mkConst (P ++ s)
  let isT := fun (b : Expr) => mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)
  let eqN := fun (a b : Expr) => mkApp3 (mkConst ``Eq [1]) natT a b
  let cP := mkLambda `s .default natT (isT (mkAppN (mkConst ``CFSG.KS.SporSch.M24.cntSl)
    #[mkConst tN, mkConst sN, lit n, lit w, mulE (mkBVar 0) (lit L), lit L, mkApp (c `C) (mkBVar 0),
      mkApp (c `C) (addE (mkBVar 0) (lit 1))]))
  let allLtE := fun (Q : Expr) => mkForall `s .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit NS])
    (Q.beta #[mkBVar 1]))
  let rflN := fun (v : Nat) => mkApp2 (mkConst ``Eq.refl [1]) natT (lit v)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `C) cs
    addDef (P ++ `NS) natT (lit NS)
    addDef (P ++ `N) natT (lit total)
    for s in [0:NS] do
      addThm (P ++ Name.mkSimple s!"c{s}") (cP.beta #[lit s])
    let hV := forallChain cP NS fun s => mkConst (P ++ Name.mkSimple s!"c{s}")
    CFSG.KC.addThmDecl <| { name := P ++ `hc, levelParams := [], type := allLtE cP, value := hV }
    let addEq := fun (nm : Name) (ty pf : Expr) =>
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := pf }
    addEq (P ++ `hc0) (eqN (mkApp (c `C) (lit 0)) (lit 0)) (rflN 0)
    addEq (P ++ `hcN) (eqN (mkApp (c `C) (c `NS)) (lit total)) (rflN total)

end
