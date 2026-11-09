module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Co1.GenVOrb
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.SporSch.Co1Full
public import Certificates.Kernel.SporSch.Co1.GenVOrb
public import CFSG.Certificates.Kernel.SporSch.Co1FibRSound

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
  let srt := pts.qsort (· < ·)
  let lowerBound := fun (v : Nat) => Id.run do
    let mut lo := 0
    let mut hi := n
    while lo < hi do
      let mid := (lo + hi) / 2
      if srt[mid]! < v then lo := mid + 1 else hi := mid
    return lo
  let rs := Array.ofFn (n := n) fun k => lowerBound (pts[k.val]! ^^^ w)
  let hpN := tN.getPrefix ++ `hp
  let hpT ← liftCoreM <| (·.type) <$> getConstInfo hpN
  let (nsE, lE) ← match hpT with
    | .forallE _ _ (.forallE _ ltE body _) _ =>
      pure (ltE.getAppArgs[3]!, (body.getAppArgs[1]!).getAppArgs[4]!)
    | _ => throwError "unexpected type of {hpN}"
  let c := fun (s : Name) => mkConst (P ++ s)
  let isT := fun (b : Expr) => mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)
  let eqN := fun (a b : Expr) => mkApp3 (mkConst ``Eq [1]) natT a b
  let slArgs := fun (s : Expr) => #[lit n, lit w, mulE s (lit L), lit L, mkApp (c `C) s,
    mkApp (c `C) (addE s (lit 1))]
  let cP := mkLambda `s .default natT (isT (mkAppN (mkConst ``CFSG.KS.SporSch.M24.cntSl)
    (#[mkConst tN, mkConst sN] ++ slArgs (mkBVar 0))))
  let rP := mkLambda `s .default natT (isT (mkAppN (mkConst ``CFSG.KS.SporSch.M24.cntSlR)
    (#[mkConst tN, mkConst sN, c `R] ++ slArgs (mkBVar 0))))
  let ltNS := fun (s : Expr) =>
    mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, s, lit NS]
  let allLtE := fun (Q : Expr) => mkForall `s .default natT (mkForall `h .default
    (ltNS (mkBVar 0)) (Q.beta #[mkBVar 1]))
  let rflN := fun (v : Nat) => mkApp2 (mkConst ``Eq.refl [1]) natT (lit v)
  let sl := slArgs (mkBVar 1)
  let hV := mkLambda `s .default natT (mkLambda `h .default (ltNS (mkBVar 0))
    (mkAppN (mkConst ``CFSG.KS.SporSch.M24.cntSl_of_R)
      #[mkConst sN, mkConst tN, c `R, lit n, nsE, lE, reflBoolTrue, reflBoolTrue, mkConst hpN,
        sl[1]!, sl[2]!, sl[3]!, sl[4]!, sl[5]!, mkApp2 (c `hcR) (mkBVar 1) (mkBVar 0)]))
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `C) cs
    addTree (P ++ `RR) (leaves rs)
    addDef (P ++ `R) fnT (strictTab (P ++ `RR))
    addDef (P ++ `NS) natT (lit NS)
    addDef (P ++ `N) natT (lit total)
    for s in [0:NS] do
      addThm (P ++ Name.mkSimple s!"c{s}") (rP.beta #[lit s])
    let hRV := forallChain rP NS fun s => mkConst (P ++ Name.mkSimple s!"c{s}")
    CFSG.KC.addThmDecl <| { name := P ++ `hcR, levelParams := [], type := allLtE rP, value := hRV }
    CFSG.KC.addThmDecl <| { name := P ++ `hc, levelParams := [], type := allLtE cP, value := hV }
    let addEq := fun (nm : Name) (ty pf : Expr) =>
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := pf }
    addEq (P ++ `hc0) (eqN (mkApp (c `C) (lit 0)) (lit 0)) (rflN 0)
    addEq (P ++ `hcN) (eqN (mkApp (c `C) (c `NS)) (lit total)) (rflN total)

end
