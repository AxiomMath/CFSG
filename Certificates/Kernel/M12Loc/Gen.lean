module

public meta import Lean
public meta import Std.Data.HashMap
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.Kernel.M12Loc
public import CFSG.Assembly.LowTwoRankDefs

namespace CertificateChecks.KernelM12Loc

open CFSG.KC.Eval CFSG.KC.M12Cent CFSG.KC.M12Loc CFSG.GH74.M12.Hyp
  CFSG.RankThree.PartTwo.Toolkit.M12

public meta def natsV (l : List Nat) : Val := .list (l.toArray.map .nat)

public meta def listsV (l : List (List Nat)) : Val := .list (l.toArray.map natsV)

public meta def locStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "locStep: expected no arguments"
  let mut seen : Std.HashMap Nat Unit := {}
  let mut conjW : Std.HashMap Nat (List Nat) := {}
  let mut queue : Array (List Nat × List Nat) := #[(tid, [])]
  seen := seen.insert (keyT tid) ()
  let mut i := 0
  while i < queue.size && conjW.size < 1320 do
    let (g, w) := queue[i]!
    i := i + 1
    let k := keyA (tmul (tmul g aT) (tinv g))
    if !conjW.contains k then conjW := conjW.insert k w
    for l in [0, 2, 3] do
      let h := tmul (letN l) g
      if !seen.contains (keyT h) then
        seen := seen.insert (keyT h) ()
        queue := queue.push (h, l :: w)
  if conjW.size != 1320 then throw "locStep: wrong count"
  let W := (conjW.toArray.qsort (fun p q => p.1 < q.1)).toList.map (·.2)
  let TT : Val := .list (trT.toArray.map listsV)
  return #[(`TT, TT), (`W, listsV W), (`TNP, listsV (idxNP.map prodT)),
    (`TNa, listsV (idxNa.map prodT))]

end CertificateChecks.KernelM12Loc
