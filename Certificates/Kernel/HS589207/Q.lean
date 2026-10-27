module

public import Certificates.Data.DcHSOut

public section

namespace CFSG.KD.HS589207

open CFSG.Quasithin.H13.LocDbl.HSLoc CFSG.Quasithin.H13.LocDbl.DcNative
  CFSG.Quasithin.H13.LocDbl.DcRank

@[expose] def qp0 : List (Nat × Nat) := [(0, 0)]

@[expose] def pk14 (l : List Nat) : Nat :=
  l.foldr (fun x acc => acc * 16384 + x) 0

@[expose] def sigOf (keys : Array Nat) : Array Nat × Array Nat :=
  let sig := (Array.range keys.size).qsort fun a b => keys[a]! < keys[b]!
  (sig, invT sig)

@[expose] def cntOf (par : Array Nat) : Array Nat := Id.run do
  let mut b : Array Nat := Array.replicate (par.size + 1) 0
  for j in [1:par.size] do
    b := b.modify par[j]! (· + 1)
  let mut out : Array Nat := #[]
  let mut acc := 1
  for k in [0:par.size] do
    out := out.push acc
    acc := acc + b[k]!
  return out

@[expose] def enM : Array Nat × Array Nat := bfsEnumL 100 B100 mTabs 12000

@[expose] def recM : Array (Array Nat) :=
  let rows := mElems.map Array.toList
  let keys := rows.map (keyNat 100 100)
  let H : Std.HashMap Nat Nat :=
    Std.HashMap.ofList ((List.range rows.size).map fun k => (keys[k]!, k))
  let so := sigOf keys
  let cnt := cntOf enM.1
  (Array.range rows.size).map fun k =>
    rows[k]!.toArray ++ #[enM.1[k]!, enM.2[k]!, cnt[k]!, so.1[k]!, so.2[k]!, 0] ++
      ((Array.range mTabs.size).map fun t => H.getD (keyNat 100 100 (rows[k]!.map (img (mTabs[t]!)))) 0)

@[expose] def fSets : Array (List Nat) :=
  (Array.range 3850).foldl (fun acc k => acc.push (if k = 0 then F0 else
    ((acc[treeF.1[k]!]!).map (img (AB.getD treeF.2[k]! #[]))).mergeSort fun a b => decide (a ≤ b)))
    #[]

@[expose] def recF : Array (Array Nat) :=
  let H : Std.HashMap (List Nat) Nat :=
    Std.HashMap.ofList ((List.range fSets.size).map fun k => (fSets[k]!, k))
  let so := sigOf (fSets.map pk14)
  (Array.range fSets.size).map fun k =>
    fSets[k]!.toArray ++ #[treeF.1[k]!, treeF.2[k]!] ++
      ((Array.range 4).map fun t =>
        H.getD (((fSets[k]!).map (img (AB.getD t #[]))).mergeSort fun a b => decide (a ≤ b)) 0) ++
      #[so.1[k]!, so.2[k]!]

@[expose] def cNodes : Array (Array Nat) :=
  (Array.range 1100).foldl (fun acc k => acc.push (if k = 0 then r0Tab else
    conjT (AB.getD cjTree.2[k]! #[]) (AB.getD (invL cjTree.2[k]!) #[]) acc[cjTree.1[k]!]!)) #[]

@[expose] def recC : Array (Array Nat) :=
  let H : Std.HashMap (List Nat) Nat :=
    Std.HashMap.ofList ((List.range cNodes.size).map fun k => (cNodes[k]!.toList, k))
  let so := sigOf (cNodes.map fun t => pk14 t.toList)
  (Array.range cNodes.size).map fun k =>
    cNodes[k]! ++ #[cjTree.1[k]!, cjTree.2[k]!] ++
      ((Array.range 4).map fun l =>
        H.getD (conjT (AB.getD l #[]) (AB.getD (invL l) #[]) cNodes[k]!).toList 0) ++
      #[so.1[k]!, so.2[k]!]

@[expose] def tabs : Array (Array Nat) :=
  #[invT ta, invT tb, wTab, r0Tab, treeElems.getD kU #[]] ++
    (goodIdx.map fun j => invT (mElems.getD j #[])).toArray ++ mTabs

@[expose] def e0Idx : List Nat :=
  (List.range mElems.size).filter fun k => F0.all fun f => img (mElems.getD k #[]) f == f

@[expose] def outIdx : List Nat :=
  (List.range mElems.size).filter fun k => e0Elems.all (commT (compT wTab (mElems.getD k #[])))

@[expose] def goodOut : List Nat :=
  goodList.map fun t => (outIdx.find? fun k => compT wTab (mElems.getD k #[]) == t).getD 0

@[expose] def idxs : Array (Array Nat) := #[e0Idx.toArray, outIdx.toArray, goodOut.toArray]

end CFSG.KD.HS589207

end
