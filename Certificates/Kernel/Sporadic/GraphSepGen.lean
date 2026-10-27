module

public import CFSG.Certificates.Kernel.Spor.GraphSepSound
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.RawTreeSound
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic

open Lean Elab Command

namespace CFSG.KS.GraphSepGen

meta def addThm (nm : Name) (ty : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }

meta def addThmV (nm : Name) (ty v : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := v }

end CFSG.KS.GraphSepGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.GraphSepGen in
elab "#ks_graphsep " pre:ident nn:num ww:num ch:num sId:ident bId:ident yy:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let CH := ch.getNat
  let y0 := yy.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let kS := S.size
  let nb := base.size
  let gens := S ++ S.map (inv n)
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  let mut seen : Std.HashSet (Nat × Nat) := {}
  let mut q : Array (Nat × Nat) := #[(0, y0)]
  seen := seen.insert (0, y0)
  let mut qi := 0
  while qi < q.size do
    let (u, v) := q[qi]!
    qi := qi + 1
    adj := adj.modify u (·.push v)
    for g in gens do
      let e := (g[u]!, g[v]!)
      if !seen.contains e then
        seen := seen.insert e
        q := q.push e
  let d := adj[0]!.size
  for a in adj do
    if a.size != d then throwError "#ks_graphsep: neighbour lists of different lengths"
  let nbm : Array Nat := adj.map fun a => a.foldl (fun acc v => acc ||| (1 <<< v)) 0
  let mut fixed : Array Bool := Array.replicate n false
  for b in base do
    fixed := fixed.set! b true
  let mut ord : Array Nat := base
  let mut wit : Array (Array Nat) := Array.replicate n #[]
  let mut cells : Array (Array Nat) := #[(List.range n).toArray.filter fun x => !fixed[x]!]
  let mut pi := 0
  while pi < ord.size do
    let a := ord[pi]!
    let na := nbm[a]!
    let mut next : Array (Array Nat) := #[]
    for C in cells do
      let inC := C.filter fun y => (na >>> y) &&& 1 == 1
      let outC := C.filter fun y => (na >>> y) &&& 1 == 0
      if inC.size > 0 && outC.size > 0 then
        for y in C do
          wit := wit.modify y (·.push (2 * pi + ((na >>> y) &&& 1)))
        next := next.push inC |>.push outC
      else
        next := next.push C
    cells := #[]
    for C in next do
      if C.size == 1 then
        fixed := fixed.set! C[0]! true
        ord := ord.push C[0]!
      else
        cells := cells.push C
    pi := pi + 1
  if ord.size != n then throwError "#ks_graphsep: the refinement fixes {ord.size} of {n} points"
  let mut wts : Array Nat := Array.replicate n 0
  for k in [nb:n] do
    let ws := wit[ord[k]!]!
    if ws.size > 255 then throwError "#ks_graphsep: {ws.size} witnesses"
    let mut R := ws.size
    for i in [0:ws.size] do
      R := R ||| (ws[i]! <<< (8 + (w + 1) * i))
    wts := wts.set! k R
  let ordP := pack w ord
  let NS := (n + CH - 1) / CH
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `PS) (S.map (pack w))
    addTree (P ++ `NB) nbm
    addTree (P ++ `AL) (adj.map (pack w))
    addTree (P ++ `WT) wts
    addDef (P ++ `ORD) natT (lit ordP)
    addDef (P ++ `BP) natT (lit (pack w base))
    let nE := lit n
    let wE := lit w
    let mE := mkApp (mkConst ``CFSG.KS.mask) wE
    let c := fun (s : Name) => mkConst (P ++ s)
    let natE := natT
    let lstP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.GraphSep.listSl)
      #[nE, wE, mE, lit d, c `NB, c `AL, mulE (mkBVar 0) (lit CH), lit CH]))
    let invB := fun (jE sE : Expr) => isTrue (mkAppN
      (mkConst ``CFSG.KS.GraphSep.invSl) #[nE, wE, mE, lit d, c `NB, c `AL, c `PS, jE,
        mulE sE (lit CH), lit CH])
    let invP := fun (jE : Expr) => mkLambda `s .default natE (invB jE (mkBVar 0))
    let refP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.GraphSep.refSl)
      #[nE, wE, mE, lit nb, c `NB, c `WT, c `ORD, mulE (mkBVar 0) (lit CH), lit CH]))
    addThm (P ++ `ord) (isTrue (mkAppN (mkConst ``CFSG.KS.GraphSep.ordK)
      #[nE, wE, mE, lit nb, c `BP, c `ORD]))
    for s in [0:NS] do
      addThm (P ++ Name.mkSimple s!"lst{s}") (mkApp lstP (lit s)).headBeta
      addThm (P ++ Name.mkSimple s!"ref{s}") (mkApp refP (lit s)).headBeta
      for j in [0:kS] do
        addThm (P ++ Name.mkSimple s!"inv{j}_{s}") (mkApp (invP (lit j)) (lit s)).headBeta
    let fa := fun (body : Expr) (k : Nat) (thm : Nat → Expr) => forallChain body k thm
    addThmV (P ++ `hL) (mkForall `s .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit NS])
        (mkApp lstP (mkBVar 1)).headBeta))
      (fa lstP NS fun s => mkConst (P ++ Name.mkSimple s!"lst{s}"))
    addThmV (P ++ `hR) (mkForall `s .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit NS])
        (mkApp refP (mkBVar 1)).headBeta))
      (fa refP NS fun s => mkConst (P ++ Name.mkSimple s!"ref{s}"))
    let invAll := mkLambda `j .default natE (mkForall `s .default natE (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit NS])
      (invB (mkBVar 2) (mkBVar 1))))
    addThmV (P ++ `hI) (mkForall `j .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit kS])
        (mkApp invAll (mkBVar 1)).headBeta))
      (fa invAll kS fun j => fa (invP (lit j)) NS fun s => mkConst (P ++ Name.mkSimple s!"inv{j}_{s}"))
