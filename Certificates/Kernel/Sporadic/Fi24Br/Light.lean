module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import Certificates.Data.Kernel.Spor.WordProgW
public import CFSG.Certificates.Kernel.Orders.Fi24p.Rels

public section

set_option maxRecDepth 400000

namespace CFSG.KD.BrFi24

open CFSG.KC.WP

@[expose] noncomputable def cv (r : Nat) : Nat := CVL.getD r 0

theorem statesL : statesOK 11 WC PS 13 = true := by quickRfl

theorem relsL : relProgsOK 11 13 PR 70 = true := by quickRfl

theorem coverL : coverAll CFSG.KD.OrdFi24p.rels WC PR 70 cv 136 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded CFSG.KD.OrdFi24p.rels 11 = true := by quickRfl

theorem relLen : CFSG.KD.OrdFi24p.rels.length = 136 :=
  Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq CFSG.KD.OrdFi24p.rels.length 136 = true)

end CFSG.KD.BrFi24

end
