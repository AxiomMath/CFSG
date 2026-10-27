module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.K3
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporDefs
public meta import Lean
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporDefs
public import Lean.Message

open Lean Elab Command

public section

namespace CFSG.KC.K3Gen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSmallLie.Child3.SelK3 CFSG.Sporadic.Schreier.Native

meta def natArr' (T : Table) : Array Nat := T.map (·.toNat)

meta def listE (l : List Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

elab "#lc_k3 " pre:ident dId:ident : command => do
  let P := pre.getId
  let D ← liftTermElabM <| unsafe evalConst Data (← liftCoreM <| realizeGlobalConstNoOverload dId)
  let n := D.n
  let w := Id.run do
    let mut w := 1
    while (1 <<< w) ≤ n + 1 do
      w := w + 1
    return w
  let pk := fun (T : Table) => pack w (natArr' T)
  let N := D.prog.length
  let R := D.regs
  let g := D.gens.size
  let mut regs := regs0 D
  let mut lw : Array Nat := Array.range R
  let mut OP := #[]; let mut A1 := #[]; let mut A2 := #[]; let mut A3 := #[]
  let mut W := #[]; let mut S1 := #[]; let mut S2 := #[]
  let mut t := 0
  for ins in D.prog do
    match ins with
    | .mu i j k =>
      OP := OP.push 0; A1 := A1.push i; A2 := A2.push j; A3 := A3.push k
      S1 := S1.push lw[i]!; S2 := S2.push lw[j]!
      let z := compT n regs[i]! regs[j]!
      W := W.push (pk z); regs := regs.set! k z; lw := lw.set! k (R + t)
    | .pwr e i k =>
      OP := OP.push 1; A1 := A1.push e; A2 := A2.push i; A3 := A3.push k
      S1 := S1.push lw[i]!; S2 := S2.push 0
      let z := powT n e regs[i]!
      W := W.push (pk z); regs := regs.set! k z; lw := lw.set! k (R + t)
    | .iv i k =>
      OP := OP.push 2; A1 := A1.push i; A2 := A2.push k; A3 := A3.push 0
      S1 := S1.push lw[i]!; S2 := S2.push 0
      let z := invT n regs[i]!
      W := W.push (pk z); regs := regs.set! k z; lw := lw.set! k (R + t)
    t := t + 1
  let A :=(D.syl.map fun r => regs[r]!).toArray
  let Ai := A.map (invT n)
  let sy := A.size
  let ord := D.order
  let E := mulClosureH n A (ord + 1)
  let Ee := E.1
  let mut idx : Std.HashMap Nat Nat := {}
  for k in [0:Ee.size] do
    idx := idx.insert (pk Ee[k]!) k
  let mut EK := #[]; let mut EKI := #[]
  for k in [0:Ee.size] do
    for l in [0:sy] do
      EK := EK.push (idx.getD (pk (compT n Ee[k]! A[l]!)) 0)
    for l in [0:sy] do
      EKI := EKI.push (idx.getD (pk (compT n Ee[k]! Ai[l]!)) 0)
  let ES := (Array.range Ee.size).qsort fun a b => (hkey n Ee[a]!).toNat < (hkey n Ee[b]!).toNat
  let mut ESI := Array.replicate Ee.size 0
  for m in [0:ES.size] do
    ESI := ESI.set! ES[m]! m
  let mut CI := #[]; let mut CE : Array Table := #[]; let mut CP := #[]; let mut CL := #[]
  let mut CK := #[]; let mut CS := #[]; let mut OFF := #[]
  let mut cpos : Std.HashMap Nat Nat := {}
  for c in [0:D.reps.length] do
    let x := Ee[D.reps[c]!]!
    let cl := conjClosureH n A Ai x (ord + 1)
    let o := CE.size
    OFF := OFF.push o
    CS := CS.push cl.1.size
    let mut loc : Std.HashMap Nat Nat := {}
    for q in [0:cl.1.size] do
      loc := loc.insert (pk cl.1[q]!) q
    for q in [0:cl.1.size] do
      let y := cl.1[q]!
      CI := CI.push c; CE := CE.push y; CP := CP.push cl.2.1[q]!; CL := CL.push cl.2.2[q]!
      if !cpos.contains (pk y) then cpos := cpos.insert (pk y) (o + q)
      for l in [0:sy] do
        CK := CK.push (loc.getD (pk (conjT n A[l]! Ai[l]! y)) 0)
  let NC := CE.size
  let ckey := fun (p : Nat) => CI[p]! * 18446744073709551616 + (hkey n CE[p]!).toNat
  let CO := (Array.range NC).qsort fun a b => ckey a < ckey b
  let mut COI := Array.replicate NC 0
  for m in [0:NC] do
    COI := COI.set! CO[m]! m
  let mut MW := #[]
  for k in [0:Ee.size] do
    let e := Ee[k]!
    if isOrd3 n e then
      match cpos.get? (pk e) with
      | some p => MW := MW.push (2 * p)
      | none => MW := MW.push (2 * (cpos.getD (pk (compT n e e)) 0) + 1)
    else MW := MW.push 0
  let wits := D.wits.toArray
  let WT := wits.map fun x => match x with | .z4 _ => 0 | .v4 _ _ => 1
  let WU := wits.map fun x => match x with | .z4 u => u | .v4 u _ => u
  let WV := wits.map fun x => match x with | .z4 _ => 0 | .v4 _ v => v
  let FR := lw
  let SY := D.syl.toArray
  let GP := D.gens.map pk
  let AIp := Ai.map pk
  liftCoreM <| withOptions (Elab.async.set · false) do
    let tr := fun (s : Name) (v : Array Nat) => addTree (P ++ s) v
    tr `OP OP; tr `A1 A1; tr `A2 A2; tr `A3 A3; tr `W W; tr `S1 S1; tr `S2 S2; tr `FR FR
    tr `GP GP; tr `SY SY; tr `AI AIp
    tr `E (Ee.map pk); tr `EP E.2.1; tr `EL E.2.2; tr `EK EK; tr `EKI EKI; tr `ES ES; tr `ESI ESI
    tr `CI CI; tr `CE (CE.map pk); tr `CP CP; tr `CL CL; tr `CK CK; tr `CO CO; tr `COI COI
    tr `MW MW; tr `WT WT; tr `WU WU; tr `WV WV
    let c := fun (s : Name) => mkConst (P ++ s)
    let lT := mkApp (mkConst ``List [0]) natT
    addDef (P ++ `CSL) lT (listE CS.toList)
    addDef (P ++ `OFFL) lT (listE OFF.toList)
    addDef (P ++ `REL) lT (listE D.reps)
    let K := mkAppN (mkConst ``CFSG.KC.K3.K3C.mk)
      #[lit n, lit w, lit R, lit g, lit N, c `OP, c `A1, c `A2, c `A3, c `W, c `S1, c `S2, c `FR,
        c `GP, lit sy, c `SY, c `AI, lit Ee.size, c `E, c `EP, c `EL, c `EK, c `EKI, c `ES, c `ESI,
        lit NC, c `CSL, c `OFFL, c `REL, c `CI, c `CE, c `CP, c `CL, c `CK, c `CO, c `COI, c `MW,
        lit wits.size, c `WT, c `WU, c `WV]
    addDef (P ++ `K) (mkConst ``CFSG.KC.K3.K3C) K
  logInfo m!"K3 sizes: n {n} w {w} N {N} R {R} ord {Ee.size} NC {NC} nw {wits.size} sy {sy}"

end CFSG.KC.K3Gen

end
