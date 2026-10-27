module

public import Certificates.Kernel.F4Levi.Data
public import Certificates.Data.Kernel.F4Levi
import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KD.F4Levi.ch799603el r (fun i => CFSG.KC.F4Levi.elN CFSG.KD.F4Levi.gs
  CFSG.KD.F4Levi.es CFSG.KD.F4Levi.ew CFSG.KD.F4Levi.nx 81 i == 1) 0 81

#kc_each CFSG.KD.F4Levi.ch799603cv r (fun i => CFSG.KC.F4Levi.cvN CFSG.KD.F4Levi.es
  CFSG.KD.F4Levi.cw CFSG.KD.F4Levi.cl CFSG.KD.F4Levi.ri CFSG.KD.F4Levi.ra i == 1) 0 81

namespace CFSG.KD.F4Levi

open CFSG.KC.F4Levi CFSG.KC.F4Syl3

theorem gen_ok : allN 6 (fun l => genN l == 1) = true := by decide +kernel

theorem d3_ok : allN 4 (d3Row dw dl gs) = true := by decide +kernel

theorem inc_ok : incB es = true := by decide +kernel

theorem es_lt : es.all (fun e => Nat.blt e (2 ^ 2704)) = true := by decide +kernel

theorem es_length : es.length = 81 := by decide +kernel

theorem ra_lt : ra.all (fun j => Nat.blt j 81) = true ∧ ra.length = 3 := by decide +kernel

theorem el_neg : elN gs es ew (nx.map fun j => (j + 1) % 81) 81 0 = 0 := by decide +kernel

theorem cv_neg : cvN es cw cl (ri.map fun r => if r < 3 then (r + 1) % 3 else r) ra
    (ri.findIdx (· < 3)) = 0 := by
  decide +kernel

theorem gen_neg : CFSG.KC.F4Salt.eqS (CFSG.KC.F4Salt.mulS (CFSG.KC.F4Salt.letS 0)
    (CFSG.KC.F4Salt.saltOf (sBits 3)))
    (CFSG.KC.F4Salt.mulS (CFSG.KC.F4Salt.saltOf (sBits 3))
      (CFSG.KC.F4Salt.letS 0)) = false ∧ lvOK 0 1 = false := by
  decide +kernel

theorem d3_neg : d3Row dw dl (gs.drop 1) 0 = false := by decide +kernel

theorem inc_neg : incB (es.take 2 ++ es.take 1) = false := by decide +kernel

end CFSG.KD.F4Levi

end
