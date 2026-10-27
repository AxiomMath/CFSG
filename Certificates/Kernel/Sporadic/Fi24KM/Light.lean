module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24KM.Data
public import Certificates.Data.Kernel.Spor.WordProgW
public import Certificates.Data.TabMThreeAFi24

public section

set_option maxRecDepth 400000

namespace CFSG.KD.KMFi24

open CFSG.KC.WP CFSG.HardMathSupport.Dickson.I271.TabMThreeA

@[expose] def cvI (j : Nat) : Nat := j

theorem statesL : statesOK 11 WC PS 29 = true := by quickRfl

theorem relsL : relProgsOK 11 29 QR 3 = true := by quickRfl

theorem movesL : relProgsOK 11 29 QM 8 = true := by quickRfl

theorem relsW : coverAll (kmRels ()) WC QR 3 cvI (kmRels ()).length = true := by quickRfl

theorem movesW : coverAll (kmMoves ()) WC QM 8 cvI (kmMoves ()).length = true := by quickRfl

theorem relsB : CFSG.KC.Ord.relsBounded (kmRels ()) 11 = true := by quickRfl

theorem movesB : CFSG.KC.Ord.relsBounded (kmMoves ()) 11 = true := by quickRfl

theorem movesLen : Nat.ble (kmMoves ()).length 8 = true := by quickRfl

end CFSG.KD.KMFi24

end
