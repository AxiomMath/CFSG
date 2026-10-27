module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshQCheck
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.CharacterTheory.Blocks.Defs
public meta import CFSG.GH74.M12.Reductions
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Data
public meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.Eval CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

public meta def packW (w : Nat) (l : List Nat) : Nat :=
  l.foldr (fun x acc => x + acc * 2 ^ w) 0

public meta def natL (xs : List Nat) : Val := .list (xs.toArray.map Val.nat)

public meta def packT (n w : Nat) (T : Table) : Nat :=
  packW w ((List.range n).map fun i => (T[i]!).toNat)

public meta def recOf (n w m cap : Nat) (gens : Array Table) : Array (Lean.Name × Val) :=
  let E := mulClosureS n m gens cap
  let L := E.1
  let cnt := L.size
  let k := gens.size
  let RL := L.toList.map (packT n w)
  let idx : Std.HashMap Nat Nat :=
    (List.range cnt).foldl (fun h i => h.insert (RL.getD i 0) i) {}
  let pos := (List.range cnt).flatMap fun h => (List.range k).map fun j =>
    idx.getD (packT n w (compT n L[h]! gens[j]!)) cnt
  let pl := (List.range cnt).flatMap fun i => [E.2.1[i]!, E.2.2[i]!]
  let km := L.map fun T => (skey m T).toNat
  let kf := L.map fun T => (hkey n T).toNat
  let sm := (Array.range cnt).qsort fun a b => km[a]! < km[b]!
  let sf := (Array.range cnt).qsort fun a b => kf[a]! < kf[b]!
  let bucket (a b : Nat) : List Nat := (List.range cnt).filterMap fun i =>
    if ((L[i]!)[0]!).toNat == a && ((L[i]!)[1]!).toNat == b then some (RL.getD i 0 * 4096 + i)
    else none
  let IX : Val := .list ((Array.range n).map fun a => .list ((Array.range n).map fun b =>
    natL (bucket a b)))
  #[(`GS, natL (gens.toList.map (packT n w))), (`RL, natL RL), (`cnt, .nat cnt),
    (`EP, .nat (packW (n * w) RL)), (`PL, .nat (packW 16 pl)), (`POS, .nat (packW 16 pos)),
    (`SM, natL sm.toList), (`SF, natL sf.toList), (`IX, IX)]

open CFSG.EvenSporadicStandard.M12Std.Yosh

public meta def argN (vs : Array Val) (i : Nat) : Nat :=
  match vs[i]? with
  | some (.nat v) => v
  | _ => 0

public meta def stepY (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  .ok (recOf 14 5 14 2000 yGens)

public meta def stepK (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  .ok (recOf 14 5 14 4000 kTabs)

public meta def stepR (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  .ok (recOf 14 5 14 4000 rTabs)

public meta def stepE (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  .ok (recOf 16 5 16 4000 eGens)

public meta def stepQ (vs : Array Val) : Except String (Array (Lean.Name × Val)) :=
  .ok (recOf 24 5 24 4000 (qGens (argN vs 0) (argN vs 1)))

public meta def stepN (vs : Array Val) : Except String (Array (Lean.Name × Val)) :=
  .ok (recOf 16 5 16 4000 (nGens (argN vs 0) (argN vs 1)))

public meta def stepNE (vs : Array Val) : Except String (Array (Lean.Name × Val)) :=
  .ok (recOf 16 5 16 4000 (nEGens (argN vs 0) (argN vs 1)))

public meta def stepW (vs : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let ws := [eWords, sWords, aWords].getD (argN vs 2) []
  .ok (recOf 16 5 16 4000 (wgens (argN vs 0) (argN vs 1) ws))

public meta def stepGE (vs : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let k := argN vs 0
  let LE := (tenum (wgens 1 k eWords)).toList
  .ok (recOf 16 5 16 4000 (LE.filter (memTab 16 (goodTabs 1 k))).toArray)

public meta def stepGL (vs : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let k := argN vs 0
  .ok (recOf 28 5 16 4000 (glueGens (wgens 1 k sWords) (sylowHomData k)))

end CertificateChecks.KernelYoshQ

end
