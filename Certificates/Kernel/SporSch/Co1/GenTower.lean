module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Co1.GenVOrb
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public import Certificates.Data.Kernel.SporSch.Co1Tower
public import Certificates.Kernel.SporSch.Co1.GenVOrb

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.GenVOrb CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native in
elab "#kss_co1tower " pre:ident dId:ident mId:ident bId:ident gId:ident sId:ident kN:num
    lN:num : command => do
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let D ← liftTermElabM <| unsafe evalConst (List (Array Nat) × List (Array Nat) × Bool) (← get dId)
  let mN ← get mId
  let B ← liftTermElabM <| unsafe evalConst (List Nat) (← get bId)
  let Gs ← liftTermElabM <| unsafe evalConst (List (List Nat)) (← get gId)
  let Ss ← liftTermElabM <| unsafe evalConst (List Nat) (← get sId)
  let K := kN.getNat
  let L := lN.getNat
  let P := pre.getId
  let cols := Array.ofFn (n := K) fun j => transposeRows 24 (D.1.getD j.val (one ()))
  for i in [0:B.length] do
    let gens := Gs.getD i []
    let n := Ss.getD i 0
    let t := vBfs cols gens (B.getD i 0) n
    if t.size != n then throwError "level {i}: {t.size} vectors, not {n}"
    let posMap : Std.HashMap Nat Nat := (List.range n).foldl (fun m k => m.insert t[k]!.1 k) {}
    let recs := t.map fun r => r.1 ||| (r.2.1 <<< 24) ||| (r.2.2 <<< 41)
    let mut es : Array Nat := #[]
    for h in [0:n] do
      for g in gens do
        es := es.push (posMap.getD (vecMulN 24 (cols.getD g #[]) t[h]!.1) n)
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
    let isT := fun (b : Expr) => mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)
    let eqN := fun (a b : Expr) => mkApp3 (mkConst ``Eq [1]) natT a b
    let lP := mkLambda `s .default natT (isT (mkAppN (mkConst ``CFSG.KS.SporSch.VOrb.levelSl)
      #[mkConst mN, gE, lit n, T, E, mulE (mkBVar 0) (lit L), lit L, mkApp C (mkBVar 0),
        mkApp C (addE (mkBVar 0) (lit 1))]))
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
        #[lit K, gE, lit (B.getD i 0), T]))
      let addEq := fun (nmE : Name) (ty pf : Expr) =>
        CFSG.KC.addThmDecl <| { name := nmE, levelParams := [], type := ty, value := pf }
      addEq (nm "hc") (eqN (mkApp C (lit 0)) (lit 1)) (rflN 1)
      addEq (nm "hn") (eqN (mkApp C (lit NS)) (lit n)) (rflN n)

end
