module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Co1.GenVOrb
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.SporSch.Co1GenB
public import Certificates.Kernel.SporSch.Co1.GenVOrb

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.GenVOrb in
elab "#kss_co1qtowerB " pre:ident tId:ident eId:ident qId:ident gId:ident bId:ident mId:ident
    kN:num lN:num : command => do
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let TT ← liftTermElabM <| unsafe evalConst (Array (Array (Nat × Nat × Nat))) (← get tId)
  let EA ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) (← get eId)
  let Qs ← liftTermElabM <| unsafe evalConst (List Nat) (← get qId)
  let Gs ← liftTermElabM <| unsafe evalConst (List (List Nat)) (← get gId)
  let BA ← liftTermElabM <| unsafe evalConst (Array Nat) (← get bId)
  let mN ← get mId
  let K := kN.getNat
  let L := lN.getNat
  let P := pre.getId
  let isT := fun (b : Expr) => mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)
  let Bc := mkConst (P ++ `B)
  let A := mkApp2 (mkConst ``CFSG.KS.SporSch.VOrb.actS) (mkConst mN) Bc
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `B) BA
    addThm (P ++ `tb) (isT (mkApp2 (mkConst ``CFSG.KC.Enum.allN) (lit 93)
      (mkLambda `g .default natT (mkApp2 (mkConst ``CFSG.KS.SporSch.VOrb.tabOK)
        (mkApp (mkConst mN) (mkBVar 0)) (mkApp Bc (mkBVar 0))))))
  for i in [0:TT.size] do
    let t := TT[i]!
    let es := EA[i]!
    let gens := Gs.getD i []
    let n := t.size
    let recs := t.map fun r => r.1 ||| (r.2.1 <<< 24) ||| (r.2.2 <<< 41)
    let ms := (Array.range n).qsort fun x y => t[x]!.1 < t[y]!.1
    let mut inv : Array Nat := Array.replicate n 0
    for k in [0:n] do
      inv := inv.set! ms[k]! k
    let srecs := Array.ofFn (n := n) fun k => ms[k.val]! ||| (inv[k.val]! <<< 17)
    let NS := (n + L - 1) / L
    let mut cs : Array Nat := #[1]
    let mut cnt := 1
    for h in [0:NS * L] do
      if h < n then
        for p in [0:gens.length] do
          if es[h * gens.length + p]! == cnt then cnt := cnt + 1
      if (h + 1) % L == 0 then cs := cs.push cnt
    let nm := fun (s : String) => P ++ Name.mkSimple s!"{s}{i}"
    let T := mkConst (nm "T")
    let E := mkConst (nm "E")
    let S := mkConst (nm "S")
    let C := mkConst (nm "C")
    let gE := toExpr gens
    let eqN := fun (a b : Expr) => mkApp3 (mkConst ``Eq [1]) natT a b
    let lP := mkLambda `s .default natT (isT (mkAppN (mkConst ``CFSG.KS.SporSch.VOrb.levelSlA)
      #[A, lit (Qs.getD i 0), gE, lit n, T, E, mulE (mkBVar 0) (lit L), lit L,
        mkApp C (mkBVar 0), mkApp C (addE (mkBVar 0) (lit 1))]))
    let pP := mkLambda `s .default natT (isT (mkAppN (mkConst ``CFSG.KS.SporSch.VOrb.permSl)
      #[S, T, lit n, mulE (mkBVar 0) (lit L), lit L]))
    let allLtE := fun (Q : Expr) => mkForall `s .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit NS])
      (Q.beta #[mkBVar 1]))
    let rflN := fun (v : Nat) => mkApp2 (mkConst ``Eq.refl [1]) natT (lit v)
    liftCoreM <| withOptions (Elab.async.set · false) do
      addTree (nm "T") (leaves recs)
      addTree (nm "E") (leaves es)
      addTree (nm "S") (leaves srecs)
      addTree (nm "C") cs
      addDef (nm "NS") natT (lit NS)
      for s in [0:NS] do
        addThm (P ++ Name.mkSimple s!"l{i}_{s}") (lP.beta #[lit s])
        addThm (P ++ Name.mkSimple s!"p{i}_{s}") (pP.beta #[lit s])
      let hlV := forallChain lP NS fun s => mkConst (P ++ Name.mkSimple s!"l{i}_{s}")
      let hpV := forallChain pP NS fun s => mkConst (P ++ Name.mkSimple s!"p{i}_{s}")
      CFSG.KC.addThmDecl <| { name := nm "hl", levelParams := [], type := allLtE lP, value := hlV }
      CFSG.KC.addThmDecl <| { name := nm "hp", levelParams := [], type := allLtE pP, value := hpV }
      addThm (nm "hd") (isT (mkAppN (mkConst ``CFSG.KS.SporSch.VOrb.levelHd)
        #[lit K, gE, lit t[0]!.1, T]))
      let addEq := fun (nmE : Name) (ty pf : Expr) =>
        CFSG.KC.addThmDecl <| { name := nmE, levelParams := [], type := ty, value := pf }
      addEq (nm "hc") (eqN (mkApp C (lit 0)) (lit 1)) (rflN 1)
      addEq (nm "hn") (eqN (mkApp C (lit NS)) (lit n)) (rflN n)

end
