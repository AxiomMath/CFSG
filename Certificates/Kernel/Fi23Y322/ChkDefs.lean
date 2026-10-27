module

public import Certificates.Data.Kernel.Fi23Y322.Defs
public import Certificates.Kernel.Fi23K.Tabs

public section

namespace CFSG.KD.Fi23Y322

open CFSG.KC.Fi23Y322 CFSG.KD.Fi23K

@[expose] def ks : List Nat := [31036, 4160, 24410, 2219, 10570, 10625, 8783, 21988]

@[expose] def edges : List (Nat × Nat) := [(0, 1), (0, 4), (0, 6), (1, 2), (2, 3), (4, 5), (6, 7)]

@[expose] def pairW (s t : Nat) : List Nat :=
  (List.replicate (if (s, t) ∈ edges then 3 else 2) [s, t]).flatten

@[expose] def relW : List (List Nat) :=
  (List.range 8).map (fun s => [s, s]) ++
    ((List.range 8).flatMap fun s => ((List.range 8).filter (s < ·)).map fun t => pairW s t) ++
    [(List.replicate 10 [0, 1, 2, 0, 4, 5, 0, 6, 7]).flatten]

@[expose] def yWords : List (List Nat) := relW.map fun w => w.map fun c => ks.getD c 0

@[expose] def w0 : List Nat := [2, 3]

@[expose] noncomputable def ychk : Bool :=
  yK G w0 ks yWords (nat_lit 31036) (nat_lit 4160)

end CFSG.KD.Fi23Y322

end
