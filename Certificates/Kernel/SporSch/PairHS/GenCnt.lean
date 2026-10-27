module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.SporSch.PairHSCnt
public import Certificates.Kernel.SporSch.GenSetReplay
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KS.SporSchCntHS

meta def natLists (j : Json) (k : String) : Except String (List (List Nat)) := do
  let a ← (← j.getObjVal? k).getArr?
  a.toList.mapM fun e => do (← e.getArr?).toList.mapM fun v => v.getNat?

meta def nats (j : Json) (k : String) : Except String (List Nat) := do
  let a ← (← j.getObjVal? k).getArr?
  a.toList.mapM fun v => v.getNat?

end CFSG.KS.SporSchCntHS

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen CFSG.KS.SporSchCntHS in
elab "#kss_cnthsdata " pre:ident ww:num jsId:ident : command => do
  let P := pre.getId
  let w := ww.getNat
  let cn (s : Ident) := liftCoreM <| realizeGlobalConstNoOverload s
  let txt ← liftTermElabM <| unsafe evalConst String (← cn jsId)
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throwError "#kss_cnthsdata: {e}"
  let lst := fun (k : String) => match natLists j k with
    | .ok l => pure l
    | .error e => throwError "#kss_cnthsdata: {k}: {e}"
  let one := fun (k : String) => match nats j k with
    | .ok l => pure l
    | .error e => throwError "#kss_cnthsdata: {k}: {e}"
  let perms ← lst "perms"
  let nfs ← lst "nfs"
  let scans ← lst "scans"
  let srch ← lst "srch"
  let nfN := fun (nf : List Nat) => pack 16 nf.toArray
  let nfRows := fun (l : List (List Nat)) => rows 64 (l.toArray.map nfN)
  let mut grp : Array (String × List (List Nat) × List (List Nat) × List Nat × List (List Nat) ×
      List (List Nat) × List (List Nat)) := #[]
  for s in ["2", "5"] do
    grp := grp.push (s, ← lst s!"r{s}", ← lst s!"p{s}", ← one s!"g{s}", ← lst s!"m{s}",
      ← lst s!"d{s}", ← lst s!"o{s}")
  liftCoreM <| withOptions (Elab.async.set · false) do
    for i in [0:perms.length] do
      addDef (P ++ Name.mkSimple s!"T{i}") natT (lit (pack w perms[i]!.toArray))
    for i in [0:nfs.length] do
      addDef (P ++ Name.mkSimple s!"n{i}") natT (lit (nfN nfs[i]!))
    for i in [0:scans.length] do
      addTree (P ++ Name.mkSimple s!"SC{i}") scans[i]!.toArray
    for i in [0:srch.length] do
      addTree (P ++ Name.mkSimple s!"V{i}") srch[i]!.toArray
    for (s, r, p, g, m, d, o) in grp do
      addTree (P ++ Name.mkSimple s!"O{s}") (rows 12 o[0]!.toArray)
      addTree (P ++ Name.mkSimple s!"OI{s}") (rows 12 o[1]!.toArray)
      addTree (P ++ Name.mkSimple s!"R{s}") (nfRows r)
      addTree (P ++ Name.mkSimple s!"P{s}") (rows 16 (p.toArray.map fun e => e[0]! + 4096 * e[1]!))
      addTree (P ++ Name.mkSimple s!"M{s}") (rows 12 (m.toArray.foldl (fun acc e => acc ++ e.toArray) #[]))
      addTree (P ++ Name.mkSimple s!"D{s}") (nfRows (d.map fun e => e.drop 1))
      addTree (P ++ Name.mkSimple s!"C{s}") (rows 2 (d.toArray.map fun e => e.headD 0))
      addTree (P ++ Name.mkSimple s!"G{s}") g.toArray
      addDef (P ++ Name.mkSimple s!"k{s}") natT (lit g.length)

end
