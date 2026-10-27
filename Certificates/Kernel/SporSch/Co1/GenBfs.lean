module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.GenBfs

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.Sporadic.SmallF2.Native

meta def emit (P : Name) (pts : Array (Array Nat)) (par lab : Array Nat) (ng : Nat)
    (step : Nat → Nat → Array Nat) : CoreM Unit := do
  let n := pts.size
  let pk := pts.map (pack 24)
  let pos : Std.HashMap Nat Nat := (List.range n).foldl (fun m k => m.insert pk[k]! k) {}
  let mut ws : Array Nat := #[]
  for h in [0:n] do
    for l in [0:ng] do
      ws := ws.push (pos.getD (pack 24 (step h l)) n)
  let srt := (Array.range n).qsort fun a b => pk[a]! < pk[b]!
  withOptions (Elab.async.set · false) do
    addTree (P ++ `P) pk
    addTree (P ++ `PAR) par
    addTree (P ++ `LAB) lab
    addTree (P ++ `W) ws
    addTree (P ++ `S) srt
    addDef (P ++ `N) natT (lit n)

end CFSG.KS.SporSch.GenBfs

open CFSG.KS.SporSch.GenBfs CFSG.Sporadic.SmallF2.Native in
elab "#kss_co1gt " pre:ident gId:ident capN:num : command => do
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let G ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let T := CFSG.Sporadic.Co1.TwoBNative.gtBFS G capN.getNat
  liftCoreM <| emit pre.getId T.pts T.par T.lab G.size fun h l => mulRows 24 T.pts[h]! G[l]!

open CFSG.KS.SporSch.GenBfs CFSG.Sporadic.SmallF2.Native in
elab "#kss_co1cts " pre:ident gId:ident giId:ident rId:ident cId:ident : command => do
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let Gs ← liftTermElabM <| unsafe evalConst (List (Array (Array Nat))) (← get gId)
  let Gis ← liftTermElabM <| unsafe evalConst (List (Array (Array Nat))) (← get giId)
  let Rs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) (← get rId)
  let Cs ← liftTermElabM <| unsafe evalConst (List Nat) (← get cId)
  for i in [0:Gs.length] do
    let G := Gs.getD i #[]
    let Gi := Gis.getD i #[]
    let c := CFSG.Sporadic.Co1.InvNative.conjBFS G Gi (Rs.getD i #[]) (Cs.getD i 0)
    liftCoreM <| emit (pre.getId ++ Name.mkSimple s!"L{i}") c.pts c.par c.lab G.size fun h l =>
      CFSG.Sporadic.Co1.InvNative.conjRows G[l]! Gi[l]! c.pts[h]!
