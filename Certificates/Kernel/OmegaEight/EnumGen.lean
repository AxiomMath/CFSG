module

public import CFSG.Certificates.Kernel.O8EnumSound
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KS.EnumGen

meta def row (a i : Nat) : Nat := (a >>> (12 * i)) % 4096

meta def low12 : Nat := 5445847423328601499764522166702896582657

meta def mul (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for l in [0:12] do
    acc := acc ^^^ ((((a >>> l) &&& low12) * 4095) &&& (row b l * low12))
  return acc

meta def idKey : Nat := Id.run do
  let mut acc := 0
  for i in [0:12] do
    acc := acc ||| (1 <<< (13 * i))
  return acc

end CFSG.KS.EnumGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.EnumGen in
elab "#ks_enum " pre:ident gId:ident : command => do
  let P := pre.getId
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let gs ← liftTermElabM <| unsafe evalConst (Array (Nat × Nat)) gN
  let ng := gs.size
  let mut seen : Std.HashMap Nat (Nat × Nat × Nat) := (∅ : Std.HashMap Nat (Nat × Nat × Nat)).insert idKey (idKey, 0, 0)
  let mut prods : Std.HashMap Nat (Array Nat) := ∅
  let mut front : Array Nat := #[idKey]
  let mut d := 0
  while !front.isEmpty do
    d := d + 1
    let mut nf : Array Nat := #[]
    for x in front do
      let mut px : Array Nat := #[]
      for j in [0:ng] do
        let z := mul x gs[j]!.1
        px := px.push z
        if !seen.contains z then
          seen := seen.insert z (x, j, d)
          nf := nf.push z
      prods := prods.insert x px
    front := nf
  let keys := (seen.toArray.map (·.1)).qsort (· < ·)
  let m := keys.size
  let idx : Std.HashMap Nat Nat := (keys.zipIdx).foldl (fun mp p => mp.insert p.1 p.2) ∅
  let mut leaves : Array Nat := #[]
  for i in [0:m] do
    let k := keys[i]!
    let (pk, g, dep) := seen.getD k (0, 0, 0)
    let mut v := k ||| (idx.getD pk 0 <<< 144) ||| (g <<< 161) ||| (dep <<< 166)
    let ks := prods.getD k #[]
    for j in [0:ng] do
      v := v ||| (idx.getD ks[j]! 0 <<< (174 + 17 * j))
    leaves := leaves.push v
  let nb := (m + 255) / 256
  let z := idx.getD idKey 0
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `D) leaves
    addTree (P ++ `G) (gs.map (·.1))
    addTree (P ++ `GI) (gs.map (·.2))
    addDef (P ++ `m) natT (lit m)
    addDef (P ++ `ng) natT (lit ng)
    addDef (P ++ `z) natT (lit z)
    addDef (P ++ `nb) natT (lit nb)
    let c := fun (s : Name) => mkConst (P ++ s)
    let headT := isTrue (mkAppN (mkConst ``CFSG.KC.O8.enumHeadOK)
      #[c `G, c `GI, lit ng, lit m, c `D, lit z])
    CFSG.KC.addThmDecl <| { name := P ++ `head, levelParams := [], type := headT, value := reflBoolTrue }
    let blkT := fun (bE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KC.O8.enumBlockOK)
      #[c `G, lit ng, lit m, c `D, bE])
    for b in [0:nb] do
      let nm := P ++ Name.mkSimple s!"blk{b}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := blkT (lit b), value := reflBoolTrue }
    let bP := mkLambda `b .default natT (blkT (mkBVar 0))
    let hbV := forallChain bP nb fun b => mkConst (P ++ Name.mkSimple s!"blk{b}")
    let hbT := mkForall `b .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit nb]) (blkT (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `blocks, levelParams := [], type := hbT, value := hbV }

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_enum_query " pre:ident q:ident qId:ident : command => do
  let P := pre.getId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  let qs ← liftTermElabM <| unsafe evalConst (Array Nat) qN
  let env ← getEnv
  let natOf := fun (n : Name) => match env.find? n with
    | some ci => (ci.value? >>= Expr.rawNatLit?).getD 0
    | none => 0
  let m := natOf (P ++ `m)
  let mut idx : Std.HashMap Nat Nat := ∅
  for k in [0:m] do
    idx := idx.insert (natOf (P ++ `D ++ Name.mkSimple s!"L{k}") % 2 ^ 144) k
  liftCoreM <| addTree q.getId (qs.map fun x => idx.getD x m)

end
