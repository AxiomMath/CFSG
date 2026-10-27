module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheckInputs
public meta import Lean
public import CFSG.Adapters.ProjectiveSpecialLinear

open Lean Elab Command

public section

namespace CFSG.KC.E3Gen

open CFSG.KC.Tab CFSG.KS.RawGen
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident
open CFSG.Sporadic.Schreier.Co3.Native

meta def firstFail (Y : Array (Array Nat)) (ws : List (List Nat × List Nat)) : Option (Nat × Nat) := Id.run do
  let mut u := 0
  for p in ws do
    let t := prodA 276 Y p.1
    let mut acc := idA 276
    let mut m := 0
    for e in p.2 do
      acc := compA 276 acc t
      if zcA acc != e then return some (u, m)
      m := m + 1
    u := u + 1
  return none

meta def code (o : Option (Nat × Nat)) : Nat :=
  match o with
  | some (u, m) => 32 * u + m
  | none => 1000000

meta def listE (l : List Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

elab "#lc_e3 " pre:ident : command => do
  let P := pre.getId
  let L := hList
  let G := gArrs
  let mut TB : Array Nat := #[]
  let mut W1 : Array Nat := #[]
  for j in [0:4608] do
    let f := firstFail #[L[j]!] wsE1
    TB := TB.push (if f.isNone then 1 else 0)
    W1 := W1.push (match f with | some (u, m) => 32 * u + m | none => 0)
  let mut reps : Array Nat := #[]
  let mut done : Array Bool := Array.replicate 4608 false
  let mut CI : Array Nat := #[]
  let mut M : Array Nat := #[]
  let mut PA : Array Nat := #[]
  let mut LB : Array Nat := #[]
  let mut CC : Array Nat := #[]
  let mut CV : Array Nat := #[]
  let mut CS : Array Nat := #[]
  let mut OFF : Array Nat := #[]
  let mut K : Array Nat := #[]
  for j in [0:4608] do
    if !done[j]! && TB[j]! == 1 then
      let k := reps.size
      reps := reps.push j
      done := done.set! j true
      let o := M.size
      OFF := OFF.push o
      let mut queue : Array (Nat × Array Nat) := #[(j, idA 276)]
      let mut qp : Array Nat := #[0]
      let mut ql : Array Nat := #[0]
      let mut q := 0
      while q < queue.size do
        let pc := queue[q]!
        q := q + 1
        for i in [0:3] do
          let g := G[i]!
          let p' := compA 276 g (compA 276 L[pc.1]! (invCand 276 g))
          let ip := hIdx p'
          if ip < 4608 && !done[ip]! then
            done := done.set! ip true
            queue := queue.push (ip, compA 276 g pc.2)
            qp := qp.push (q - 1)
            ql := ql.push i
      let mut loc : Std.HashMap Nat Nat := {}
      for t in [0:queue.size] do
        loc := loc.insert queue[t]!.1 t
      for t in [0:queue.size] do
        let (e, c) := queue[t]!
        CI := CI.push k
        M := M.push e
        PA := PA.push qp[t]!
        LB := LB.push ql[t]!
        CC := CC.push (pack 9 c)
        CV := CV.push (hIdx (invCand 276 c))
        for i in [0:3] do
          let g := G[i]!
          let p' := compA 276 g (compA 276 L[e]! (invCand 276 g))
          K := K.push (loc.getD (hIdx p') 0)
      CS := CS.push queue.size
  let N := M.size
  let mut MI' : Array Nat := Array.replicate 4608 N
  for p in [0:N] do
    MI' := MI'.set! M[p]! p
  let mut W2 : Array Nat := #[]
  let mut P2 : Array Nat := #[]
  for k in [0:reps.size] do
    for j2 in [0:4608] do
      let f := firstFail #[L[reps[k]!]!, L[j2]!] wsE2
      W2 := W2.push (code f)
      if f.isNone then P2 := P2.push (4608 * k + j2)
  let mut W3 : Array Nat := #[]
  let mut P3 : Array Nat := #[]
  for t in [0:P2.size] do
    let k := P2[t]! / 4608
    let j2 := P2[t]! % 4608
    for j3 in [0:4608] do
      let f := firstFail #[L[reps[k]!]!, L[j2]!, L[j3]!] wsE3
      W3 := W3.push (code f)
      if f.isNone then P3 := P3.push (4608 * t + j3)
  let cent := (List.range 4608).filter fun k => commutesA 276 L[k]! yArr
  let mut LK : Array Nat := #[]
  let mut LI : Array Nat := #[]
  let mut LY : Array Nat := #[]
  let mut LW : Array Nat := #[]
  for t3 in [0:P3.size] do
    let t := P3[t3]! / 4608
    let j3 := P3[t3]! % 4608
    let k := P2[t]! / 4608
    let j2 := P2[t]! % 4608
    let Y := #[L[reps[k]!]!, L[j2]!, L[j3]!]
    if psiFormOK Y then
      let i := ((List.range 4608).find? fun i => (List.range 3).all fun m =>
        eqA 276 (compA 276 L[i]! psiGArrs[m]!) (compA 276 Y[m]! L[i]!)).getD 0
      LK := LK.push 0
      LI := LI.push i
      LY := LY.push 0
      for _ in [0:6 * 128] do
        LW := LW.push 0
    else
      let T := sigmaTab Y
      let jh := ((List.range 4608).find? fun jh =>
        let h := L[jh]!
        let hi := invCand 276 h
        let iy := hIdx (compA 276 h (compA 276 yArr hi))
        decide (iy < 4608) && eqA 276 (compA 276 L[iy]! h) (compA 276 h yArr) && eqA 276 T[iy]! yArr &&
          cent.all fun kk => (List.range 4608).any fun j₀ =>
            commutesA 276 L[j₀]! yArr && chainBad T h hi j₀ kk).getD 0
      let h := L[jh]!
      let hi := invCand 276 h
      LK := LK.push 1
      LI := LI.push jh
      LY := LY.push (hIdx (compA 276 h (compA 276 yArr hi)))
      for kk in cent do
        let j₀ := ((List.range 4608).find? fun j₀ =>
          commutesA 276 L[j₀]! yArr && chainBad T h hi j₀ kk).getD 0
        let i1 := hIdx (compA 276 h (compA 276 L[j₀]! hi))
        let x1 := compA 276 bcbArr (compA 276 T[i1]! bcbArr)
        let i1' := hIdx x1
        let i2 := hIdx (compA 276 h (compA 276 L[i1']! hi))
        let x2 := compA 276 bcbArr (compA 276 T[i2]! bcbArr)
        let i2' := hIdx x2
        let i3 := hIdx (compA 276 h (compA 276 L[i2']! hi))
        LW := LW ++ #[j₀, i1, i1', i2, i2', i3]
  let mut DD : Array Nat := #[0]
  for j in [1:4608] do
    DD := DD.push (DD[hPar[j]!]! + 1)
  let wsT := toTypeExpr (List (List Nat × List Nat))
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `WS1) wsT (toExpr wsE1)
    addDef (P ++ `WS2) wsT (toExpr wsE2)
    addDef (P ++ `WS3) wsT (toExpr wsE3)
    addTree (P ++ `TB) TB
    addTree (P ++ `W1) W1
    addDef (P ++ `CS) (mkApp (mkConst ``List [0]) natT) (listE CS.toList)
    addDef (P ++ `OFF) (mkApp (mkConst ``List [0]) natT) (listE OFF.toList)
    addTree (P ++ `CI) CI
    addTree (P ++ `M) M
    addTree (P ++ `PA) PA
    addTree (P ++ `LB) LB
    addTree (P ++ `CC) CC
    addTree (P ++ `CV) CV
    addTree (P ++ `K) K
    addTree (P ++ `MI) MI'
    addDef (P ++ `N) natT (lit N)
    addDef (P ++ `R) (mkApp (mkConst ``List [0]) natT) (listE reps.toList)
    addTree (P ++ `W2) W2
    addDef (P ++ `P2) (mkApp (mkConst ``List [0]) natT) (listE P2.toList)
    addTree (P ++ `W3) W3
    addDef (P ++ `P3) (mkApp (mkConst ``List [0]) natT) (listE P3.toList)
    addDef (P ++ `LK) (mkApp (mkConst ``List [0]) natT) (listE LK.toList)
    addDef (P ++ `LI) (mkApp (mkConst ``List [0]) natT) (listE LI.toList)
    addDef (P ++ `LY) (mkApp (mkConst ``List [0]) natT) (listE LY.toList)
    addTree (P ++ `LW) LW
    addTree (P ++ `DD) DD

end CFSG.KC.E3Gen

end
