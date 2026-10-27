module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuY2Inputs
public import CFSG.Assembly.LowTwoRankDefs

namespace CFSG.KD.LQT.C4163

open CFSG.KC.Eval CFSG.Quasithin.A312Ru CFSG.QuasithinUnique.Ch1.SporLat

meta def packT (t : Array Nat) : Nat :=
  (List.range t.size).foldl (fun acc i => acc ||| (t[i]! <<< (12 * i))) 0

public meta def stepG (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "stepG: expected no arguments"
  let n := 4060
  let gs := ruQuot2.map fun x => packT (quotGt n ruQuotL2 x)
  let is := ruQuot2.map fun x => packT (quotGi n ruQuotL2 x)
  return #[(`GC, .list ((gs ++ is).toArray.map .nat))]

end CFSG.KD.LQT.C4163
