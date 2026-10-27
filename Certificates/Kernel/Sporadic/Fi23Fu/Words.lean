module

public import Certificates.Data.CFSGNative.Fi23.Data

public section

namespace CFSG.KD.Fi23Fu

@[expose] def chainL (z : Int) : Nat × Bool := (z.natAbs + 9, decide (0 < z))

@[expose] def kleinL (l : Nat) : Nat × Bool := (l / 2 + 12, Nat.beq (l % 2) 0)

@[expose] def kleinZW : List Nat :=
  [19, 7, 3, 0, 13, 19, 7, 4, 15, 8, 14, 9, 22, 18, 13, 20, 18, 16, 16]

@[expose] def wW : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (7, true), (8, true)]

@[expose] def uInvW : List (Nat × Bool) :=
  [(8, false), (7, false), (4, false), (3, false), (2, false), (1, false),
    (8, false), (7, false), (4, false), (3, false), (2, false), (1, false),
    (8, false), (7, false), (4, false), (3, false), (2, false), (1, false),
    (8, false), (7, false), (4, false), (3, false), (2, false), (1, false)]

@[expose] def vW : List (Nat × Bool) :=
  [(2, true), (9, true), (11, false), (1, true), (10, true), (11, true), (6, true), (4, true),
    (5, true), (1, true)]

@[expose] def vInvW : List (Nat × Bool) :=
  [(1, false), (5, false), (4, false), (6, false), (11, false), (10, false), (1, false),
    (11, true), (9, false), (2, false)]

@[expose] def relsF : List (List (Nat × Bool)) :=
  ((CFSG.Sporadic.Fi23.Native.chainWords ()).toList.zipIdx.map fun (w, j) =>
      w.map chainL ++ [(j + 12, false)]) ++
    [kleinZW.map kleinL ++ vW ++ uInvW ++ vInvW,
      wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW]

end CFSG.KD.Fi23Fu

end
