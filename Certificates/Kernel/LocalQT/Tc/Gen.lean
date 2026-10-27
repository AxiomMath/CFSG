module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KD.LQT.TcGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def idArr (n : Nat) : Array Nat := Array.range n

meta def refN (n : Nat) (ns : Array (Array Nat × Array Nat)) (z : Int) : Array Nat × Array Nat :=
  if z = 0 then (idArr n, idArr n)
  else if 0 < z then ns[z.toNat - 1]!
  else let p := ns[(-z).toNat - 1]!; (p.2, p.1)

meta def push (n : Nat) (ns : Array (Array Nat × Array Nat)) (a b : Int) :
    Array (Array Nat × Array Nat) :=
  let A := refN n ns a
  let B := refN n ns b
  ns.push (comp n A.1 B.1, comp n B.2 A.2)

meta def word (n : Nat) (ns : Array (Array Nat × Array Nat)) (wd : List Int) :
    Array (Array Nat × Array Nat) × Int := Id.run do
  let mut ns := ns
  let mut r : Int := 0
  for z in wd.reverse do
    ns := push n ns z r
    r := Int.ofNat ns.size
  return (ns, r)

meta def progN (n : Nat) (ns : Array (Array Nat × Array Nat)) (regs : Array Nat)
    (prog : List (Int × Int)) : Array (Array Nat × Array Nat) := Id.run do
  let mut ns := ns
  let mut regs := regs
  for pq in prog do
    let rr := fun (z : Int) => if z = 0 then (0 : Int)
      else if 0 < z then (if z.toNat - 1 < regs.size then Int.ofNat (regs[z.toNat - 1]! + 1) else 0)
      else (if (-z).toNat - 1 < regs.size then Int.negSucc regs[(-z).toNat - 1]! else 0)
    let a := rr pq.1
    let b := rr pq.2
    ns := push n ns a b
    regs := regs.push (ns.size - 1)
  return ns

meta def layMCN (n : Nat) (gs ts : List (Array Nat × Array Nat)) (ws : List (List Int))
    (prog : List (Int × Int)) : Array (Array Nat × Array Nat) := Id.run do
  let g := gs.length
  let mut ns : Array (Array Nat × Array Nat) := (gs ++ ts).toArray
  let mut regs : Array Nat := #[]
  for wd in ws do
    let (ns', r) := word n ns wd
    ns := ns'
    for e in [0:ts.length] do
      ns := push n ns r (Int.ofNat (g + e + 1))
      ns := push n ns (Int.ofNat ns.size) (-r)
      regs := regs.push (ns.size - 1)
  return progN n ns regs prog

meta def addNodes (P : Name) (w : Nat) (ns : Array (Array Nat × Array Nat)) : CoreM Unit := do
  addTree (P ++ `X) (ns.map fun p => pack w p.1)
  addTree (P ++ `XI) (ns.map fun p => pack w p.2)

meta def natListE (l : Array Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

meta def listNatT : Expr := mkApp (mkConst ``List [0]) natT

end CFSG.KD.LQT.TcGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KD.LQT.TcGen in
elab "#kqb_mc " pre:ident nn:num ww:num gId:ident tId:ident wsId:ident pId:ident : command => do
  let n := nn.getNat
  let w := ww.getNat
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let gs ← liftTermElabM <| unsafe evalConst (List (Array Nat × Array Nat)) (← get gId)
  let ts ← liftTermElabM <| unsafe evalConst (List (Array Nat × Array Nat)) (← get tId)
  let ws ← liftTermElabM <| unsafe evalConst (List (List Int)) (← get wsId)
  let prog ← liftTermElabM <| unsafe evalConst (List (Int × Int)) (← get pId)
  withSync <| addNodes pre.getId w (layMCN n gs ts ws prog)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KD.LQT.TcGen in
elab "#kqb_run " pre:ident nn:num ww:num gId:ident pId:ident : command => do
  let n := nn.getNat
  let w := ww.getNat
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let gs ← liftTermElabM <| unsafe evalConst (List (Array Nat × Array Nat)) (← get gId)
  let prog ← liftTermElabM <| unsafe evalConst (List (Int × Int)) (← get pId)
  withSync <| addNodes pre.getId w (progN n gs.toArray (Array.range gs.length) prog)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KD.LQT.TcGen in
elab "#kqb_syl " pre:ident nn:num ww:num NN:num gId:ident parId:ident labId:ident tabId:ident :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let N := NN.getNat
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let gs ← liftTermElabM <| unsafe evalConst (List (Array Nat × Array Nat)) (← get gId)
  let par ← liftTermElabM <| unsafe evalConst (List Nat) (← get parId)
  let lab ← liftTermElabM <| unsafe evalConst (List Nat) (← get labId)
  let tab ← liftTermElabM <| unsafe evalConst (List Nat) (← get tabId)
  let ng := gs.length
  let G := gs.toArray
  let PA := (Array.range N).map fun k => par.getD k 0
  let LA := (Array.range N).map fun k => lab.getD k 0
  let TA := (Array.range (N * ng)).map fun k => tab.getD k 0
  let mut Al : Array (Array Nat) := #[]
  for k in [0:N] do
    if k = 0 then Al := Al.push (idArr n)
    else Al := Al.push (comp n Al[PA[k]!]! G[LA[k]!]!.1)
  let E := Al.map (pack w)
  let ord := (Array.range N).qsort fun a b => E[a]! < E[b]!
  let mut rank := Array.replicate N 0
  for j in [0:N] do
    rank := rank.set! ord[j]! j
  withSync do
    addTree (P ++ `E) E
    addTree (P ++ `PT) PA
    addTree (P ++ `LT) LA
    addTree (P ++ `TB) TA
    addTree (P ++ `IS) ord
    addTree (P ++ `SR) rank
    addDef (P ++ `G) listNatT (natListE (G.map fun g => pack w g.1))
    addDef (P ++ `GI) listNatT (natListE (G.map fun g => pack w g.2))
    addDef (P ++ `ParL) listNatT (natListE par.toArray)
    addDef (P ++ `LabL) listNatT (natListE lab.toArray)
    addDef (P ++ `TabL) listNatT (natListE tab.toArray)

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kqb_idx " pre:ident NN:num gg:num bb:num gbb:num tabId:ident parId:ident labId:ident
    repsId:ident : command => do
  let P := pre.getId
  let N := NN.getNat
  let ng := gg.getNat
  let b := bb.getNat
  let gb := gbb.getNat
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let tab ← liftTermElabM <| unsafe evalConst (List Nat) (← get tabId)
  let par ← liftTermElabM <| unsafe evalConst (List Nat) (← get parId)
  let lab ← liftTermElabM <| unsafe evalConst (List Nat) (← get labId)
  let reps ← liftTermElabM <| unsafe evalConst (List (Nat × Nat)) (← get repsId)
  let TA := tab.toArray
  let PA := par.toArray
  let LA := lab.toArray
  let mut mt : Array (Array Nat) := #[]
  for i in [0:N] do
    let mut row : Array Nat := #[]
    for j in [0:N] do
      row := row.push (if j = 0 then i else
        TA.getD (row[PA.getD j 0]! * ng + LA.getD j 0) 0)
    mt := mt.push row
  let mul := fun (i j : Nat) => mt[i]![j]!
  let inv := (Array.range N).map fun s => ((List.range N).findIdx? fun j => mul s j == 0).getD N
  let isInv := fun (k : Nat) => k != 0 && mul k k == 0
  let conj := fun (s i : Nat) => mul (mul s i) inv[s]!
  let inFg := fun (a b u : Nat) => u == a || u == b || u == mul a b
  let RA := reps.toArray
  let mut gw : Array (Array Nat) := #[]
  for i in [0:N] do
    let mut row : Array Nat := Array.replicate N 0
    if isInv i then
      for j in [0:N] do
        if isInv j && mul i j == mul j i then
          let mut found := 0
          for a in [0:RA.size] do
            if found == 0 then
              for s in [0:N] do
                if found == 0 then
                  let ci := conj s i
                  let cj := conj s j
                  if ci != cj && inFg RA[a]!.1 RA[a]!.2 ci && inFg RA[a]!.1 RA[a]!.2 cj then
                    found := 1 + a * 256 + s
          row := row.set! j found
    gw := gw.push row
  withSync do
    addTree (P ++ `MR) (mt.map (pack b))
    addTree (P ++ `IT) inv
    addTree (P ++ `GW) (gw.map (pack gb))

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kqb_range " pre:ident fId:ident lo:num hi:num : command => do
  let P := pre.getId
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  withSync do
    for i in [lo.getNat:hi.getNat] do
      let nm := P ++ Name.mkSimple s!"c{i}"
      let tyI := isTrue (mkApp (mkConst fN) (lit i))
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyI, value := reflBoolTrue }

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kqb_all " pre:ident fId:ident kk:num : command => do
  let P := pre.getId
  let k := kk.getNat
  let fE := mkConst (← liftCoreM <| realizeGlobalConstNoOverload fId)
  withSync do
    let pE := mkLambda `i .default natT (isTrue (mkApp fE (mkBVar 0)))
    let v := forallChain pE k fun i => mkConst (P ++ Name.mkSimple s!"c{i}")
    let ty := mkForall `i .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit k])
      (isTrue (mkApp fE (mkBVar 1))))
    CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := ty, value := v }

end
