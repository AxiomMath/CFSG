module

public import Certificates.Data.Kernel.TabMatGrp
public import Certificates.Kernel.LocalComp.J3Seeds
public import Certificates.Data.J3E27.Words
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ3E27

open CFSG.KC.TabMatGrp CertificateChecks.KernelLC.J3Ops

@[expose] def toF2 (l : Nat × Bool) : Fin 2 × Bool := (if l.1 = 0 then 0 else 1, l.2)

@[expose] def segs : List (List (Fin 2 × Bool)) :=
  [J3E27.wordW1, J3E27.wordX3, J3E27.wordS, J3E27.wordT].map (List.map toF2)

@[expose] def sW1 : List (Fin 4 × Bool) := [(0, true)]

@[expose] def sW1i : List (Fin 4 × Bool) := [(0, false)]

@[expose] def sW2 : List (Fin 4 × Bool) := [(2, true), (0, true), (2, false)]

@[expose] def sW2i : List (Fin 4 × Bool) := [(2, true), (0, false), (2, false)]

@[expose] def sX3 : List (Fin 4 × Bool) := [(1, true)]

@[expose] def sX3i : List (Fin 4 × Bool) := [(1, false)]

@[expose] def sS : List (Fin 4 × Bool) := [(2, true)]

@[expose] def sSi : List (Fin 4 × Bool) := [(2, false)]

@[expose] def sT : List (Fin 4 × Bool) := [(3, true)]

@[expose] def sTi : List (Fin 4 × Bool) := [(3, false)]

@[expose] def rels : List (List (Fin 4 × Bool) × List (Fin 2 × Bool)) :=
  [(sW1 ++ sW1 ++ sW1, []), (sW2 ++ sW2 ++ sW2, []), (sX3 ++ sX3 ++ sX3, []),
    (sW1 ++ sW2 ++ sW1i ++ sW2i, []), (sW1 ++ sX3 ++ sW1i ++ sX3i, []),
    (sW2 ++ sX3 ++ sW2i ++ sX3i, []), (sS ++ sW2 ++ sSi ++ sW2i ++ sW1i, []),
    (sS ++ sX3 ++ sSi ++ sX3, []), (sT ++ sW1 ++ sTi ++ sW1, []), (sT ++ sW2 ++ sTi ++ sW2, []),
    (sT ++ sX3 ++ sTi ++ sX3i, [])]

@[expose] def rep (k : Nat) (w : List (Fin 4 × Bool)) : List (Fin 4 × Bool) :=
  (List.replicate k w).flatten

@[expose] def prodW (n : Nat) : List (Fin 4 × Bool) :=
  rep (n / 9) sW1 ++ rep (n / 3 % 3) sW2 ++ rep (n % 3) sX3

@[expose] def prods : List (List (Fin 4 × Bool)) := (List.range 27).map prodW

theorem ch810202rel : grpK 80 SA.M SB.M 2 3 (segs.map natW)
    (rels.map fun q => (natW q.1, natW q.2)) = true := by
  quickRfl

theorem ch810202dist : distK 80 SA.M SB.M 2 3 (segs.map natW) (prods.map natW) = true := by
  quickRfl

end CertificateChecks.KernelJ3E27

end
