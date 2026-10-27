module

public meta import Lean
public meta import Std.Data.HashMap
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.RankThree.PartTwo.Toolkit.M12LocalInputs
public meta import Certificates.Data.Kernel.M12Cent
public import CFSG.Assembly.LowTwoRankDefs

namespace CertificateChecks.KernelM12Cent

open CFSG.KC.Eval CFSG.KC.M12Cent CFSG.GH74.M12.Hyp

public meta def natsV (l : List Nat) : Val := .list (l.toArray.map .nat)

public meta def wordsV (l : List (List Nat)) : Val := .list (l.toArray.map natsV)

public meta def centStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "centStep: expected no arguments"
  let z := CFSG.RankThree.PartTwo.Toolkit.M12.zT
  let S := CFSG.RankThree.PartTwo.Toolkit.M12.ET ++ CFSG.RankThree.PartTwo.Toolkit.M12.FT
  let mut seen : Std.HashMap Nat Unit := {}
  let mut conjW : Std.HashMap Nat (List Nat) := {}
  let mut cent : Array (Nat × List Nat) := #[]
  let mut queue : Array (List Nat × List Nat) := #[(tid, [])]
  seen := seen.insert (keyT tid) ()
  let mut i := 0
  while i < queue.size && (conjW.size < 1760 || cent.size < 54) do
    let (g, w) := queue[i]!
    i := i + 1
    let cz := tmul (tmul g z) (tinv g)
    if !conjW.contains (keyT cz) then conjW := conjW.insert (keyT cz) w
    if cent.size < 54 && tmul g z == tmul z g then cent := cent.push (keyT g, w)
    for l in [0, 2, 3] do
      let h := tmul (letN l) g
      if !seen.contains (keyT h) then
        seen := seen.insert (keyT h) ()
        queue := queue.push (h, l :: w)
  if conjW.size != 1760 || cent.size != 54 then throw "centStep: wrong counts"
  let W := (conjW.toArray.qsort (fun p q => p.1 < q.1)).toList.map (·.2)
  let C := (cent.qsort (fun p q => p.1 < q.1)).toList.map (·.2)
  let mut R : Array (List Nat) := #[]
  for s in S do
    if s == tid then R := R.push [] else
      match conjW.get? (keyT s) with
      | some w => R := R.push w
      | none => throw "centStep: a table of S is not a conjugate of z"
  return #[(`t, natsV z), (`S, wordsV S), (`W, wordsV W), (`C, wordsV C), (`R, wordsV R.toList)]

end CertificateChecks.KernelM12Cent
