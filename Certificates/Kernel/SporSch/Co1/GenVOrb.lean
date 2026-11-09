module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.Kernel.SporSch.Co1VOrb
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.SporSch.Co1GenBSound

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.GenVOrb

open CFSG.KC.Tab CFSG.KS.RawGen

meta def addE (a b : Expr) : Expr :=
  mkAppN (mkConst ``HAdd.hAdd [0, 0, 0])
    #[natT, natT, natT, mkApp2 (mkConst ``instHAdd [0]) natT (mkConst ``instAddNat), a, b]

meta def leaves (rs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for j in [0:(rs.size + 31) / 32] do
    let mut acc := 0
    for t in [0:32] do
      acc := acc ||| (rs.getD (32 * j + t) 0 <<< (64 * t))
    out := out.push acc
  return out

meta def addThm (nm : Name) (ty : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }

meta def strictTab (R : Name) : Expr :=
  mkLambda `j .default natT (mkApp2 (mkConst ``CFSG.KC.Enum.strictN) (mkBVar 0)
    (mkLambda `i .default natT (mkApp2 (mkConst ``Nat.lor) (mkApp (mkConst R) (mkBVar 0)) (lit 0))))

end CFSG.KS.SporSch.GenVOrb

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.GenVOrb CFSG.Sporadic.SmallF2.Native in
elab "#kss_vorb " pre:ident aId:ident bId:ident v0N:num nN:num lN:num : command => do
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let A ← liftTermElabM <| unsafe evalConst Nat aN
  let B ← liftTermElabM <| unsafe evalConst Nat bN
  let v0 := v0N.getNat
  let n := nN.getNat
  let L := lN.getNat
  let P := pre.getId
  let rows := fun (X : Nat) => Array.ofFn (n := 24) fun i => (X >>> (24 * i.val)) &&& 16777215
  let O := vOrbitBFS 24 (transposeRows 24 (rows A)) (transposeRows 24 (rows B)) v0 n
  if O.pts.size != n then throwError "the orbit has {O.pts.size} vectors, not {n}"
  let recs := Array.ofFn (n := n) fun k =>
    O.pts[k]! ||| ((O.alpha[k]!).toNat <<< 24) ||| ((O.beta[k]!).toNat <<< 41)
  let ms := (Array.range n).qsort fun x y => O.pts[x]! < O.pts[y]!
  let mut inv : Array Nat := Array.replicate n 0
  for k in [0:n] do
    inv := inv.set! ms[k]! k
  let srecs := Array.ofFn (n := n) fun k => ms[k.val]! ||| (inv[k.val]! <<< 17)
  let NS := (n + L - 1) / L
  let mut cs : Array Nat := #[1]
  let mut cnt := 1
  for h in [0:NS * L] do
    if h < n then
      if (O.alpha[h]!).toNat == cnt then cnt := cnt + 1
      if (O.beta[h]!).toNat == cnt then cnt := cnt + 1
    if (h + 1) % L == 0 then cs := cs.push cnt
  let c := fun (s : Name) => mkConst (P ++ s)
  let tab := fun (X : Nat) => (List.range 96).foldl (fun acc e => acc |||
    (vecMulN 24 (transposeRows 24 (rows X)) ((e % 16) <<< (4 * (e / 16))) <<< (24 * e))) 0
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `TR) (leaves recs)
    addDef (P ++ `T) fnT (strictTab (P ++ `TR))
    addDef (P ++ `BA) natT (lit (tab A))
    addDef (P ++ `BB) natT (lit (tab B))
    addTree (P ++ `SR) (leaves srecs)
    addDef (P ++ `S) fnT (strictTab (P ++ `SR))
    addTree (P ++ `C) cs
    addDef (P ++ `NS) natT (lit NS)
    let isT := fun (b : Expr) => mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)
    let eqN := fun (a b : Expr) => mkApp3 (mkConst ``Eq [1]) natT a b
    let bP := mkLambda `s .default natT (isT (mkAppN (mkConst ``CFSG.KS.SporSch.VOrb.bfsSl)
      #[mkConst aN, mkConst bN, c `T, lit n, mulE (mkBVar 0) (lit L), lit L, mkApp (c `C) (mkBVar 0),
        mkApp (c `C) (addE (mkBVar 0) (lit 1))]))
    let pP := mkLambda `s .default natT (isT (mkAppN (mkConst ``CFSG.KS.SporSch.VOrb.permSl)
      #[c `S, c `T, lit n, mulE (mkBVar 0) (lit L), lit L]))
    addThm (P ++ `ta) (isT (mkApp2 (mkConst ``CFSG.KS.SporSch.VOrb.tabOK) (mkConst aN) (c `BA)))
    addThm (P ++ `tb) (isT (mkApp2 (mkConst ``CFSG.KS.SporSch.VOrb.tabOK) (mkConst bN) (c `BB)))
    for s in [0:NS] do
      let bV := mkAppN (mkConst ``CFSG.KS.SporSch.VOrb.bfsSl_of_tab)
        #[mkConst aN, mkConst bN, c `BA, c `BB, c `T, lit n, mulE (lit s) (lit L), lit L,
          mkApp (c `C) (lit s), mkApp (c `C) (addE (lit s) (lit 1)), c `ta, c `tb, reflBoolTrue]
      let bT := bP.beta #[lit s]
      let sN := P ++ Name.mkSimple s!"b{s}"
      CFSG.KC.addThmDecl { name := sN, levelParams := [], type := bT, value := bV }
      addThm (P ++ Name.mkSimple s!"p{s}") (pP.beta #[lit s])
    let allLtE := fun (Q : Expr) => mkForall `s .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit NS])
      (Q.beta #[mkBVar 1]))
    let hbV := forallChain bP NS fun s => mkConst (P ++ Name.mkSimple s!"b{s}")
    let hpV := forallChain pP NS fun s => mkConst (P ++ Name.mkSimple s!"p{s}")
    CFSG.KC.addThmDecl <| { name := P ++ `hb, levelParams := [], type := allLtE bP, value := hbV }
    CFSG.KC.addThmDecl <| { name := P ++ `hp, levelParams := [], type := allLtE pP, value := hpV }
    let rflN := fun (v : Nat) => mkApp2 (mkConst ``Eq.refl [1]) natT (lit v)
    let addEq := fun (nm : Name) (ty pf : Expr) =>
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := pf }
    addEq (P ++ `hr) (eqN (mkApp2 (mkConst ``CFSG.KS.SporSch.VOrb.ptK) (c `T) (lit 0)) (lit v0))
      (rflN v0)
    addEq (P ++ `hc0) (eqN (mkApp (c `C) (lit 0)) (lit 1)) (rflN 1)
    addEq (P ++ `hcN) (eqN (mkApp (c `C) (c `NS)) (lit n)) (rflN n)

end
