module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairDataE7
public import Certificates.Data.Kernel.PairBnb
import CFSG.Certificates.Kernel.PairBnbSound
import CFSG.Certificates.Kernel.Common.ForallTree
import Certificates.Kernel.E7Pair.Nb
import Certificates.Kernel.E7Pair.Chk1
import Certificates.Kernel.E7Pair.Chk2A
import Certificates.Kernel.E7Pair.Chk2B
import Certificates.Kernel.E7Pair.Chk2C
import Certificates.Kernel.E7Pair.Chk2D
import Certificates.Kernel.E7Pair.Chk2E
import Certificates.Kernel.E7Pair.Chk2F
import Certificates.Kernel.E7Pair.Chk2G

public section

namespace Certificates.Kernel.E7Pair

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.KC.PairBnb

#kc_forall_tree e7c1All (fun i => bnbR (nbP (packT e7Nb)) (wtF 56 1 1) e7O1 200
  (rootMask 56 119 e7Nb i) 44 = true) 63 ch129090a.i

#kc_forall_tree e7c2All (fun i => bnbR (nbP (packT e7Nb)) (wtF 56 2 1) e7O2 200
  (rootMask 56 119 e7Nb i) 53 = true) 63 ch129090b.i

theorem e7_neg : bnbR (nbP (packT e7Nb)) (wtF 56 1 1) e7O1 200 (rootMask 56 119 e7Nb 62) 0 = false := by
  decide +kernel

theorem e7_nbP_lt : ∀ v < 119, nbP (packT e7Nb) v = e7Nb.getD v 0 := by
  decide +kernel

theorem e7_packT_lt : packT e7Nb < 2 ^ 15232 := by
  decide +kernel

theorem e7_nbP (v : Nat) : nbP (packT e7Nb) v = e7Nb.getD v 0 := by
  rcases Nat.lt_or_ge v 119 with h | h
  · exact e7_nbP_lt v h
  · have hl : e7Nb.length = 119 := rfl
    rw [nbP_of_lt _ v 15232 e7_packT_lt (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega)]
    rfl

theorem e7Check_holds : e7Check := by
  refine ⟨e7_nb_ok, fun i hi => ?_, fun i hi => ?_⟩
  · rw [← bnbR_pairGraph _ e7Nb 1 1 _ e7_nbP]
    exact e7c1All i hi
  · rw [← bnbR_pairGraph _ e7Nb 2 1 _ e7_nbP]
    exact e7c2All i hi

end Certificates.Kernel.E7Pair
