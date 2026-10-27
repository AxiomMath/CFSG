module

public import Certificates.Kernel.Sporadic.OddCore.HNPairC
public import Certificates.Kernel.Sporadic.OddCore.HN2092
public import Certificates.Kernel.HS100.Chain
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HNPair

open CFSG.RankThree.PartOne.HNRed.Native CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelHS100

theorem dPC : allN 9 (fun j => permOK 1200 11 (mask 11) (1200 * 11) (HPD.S j) (HPD.SI j)) = true := by
  quickRfl

theorem pairK : allN 2 (fun j => bAnd(allN 1100 (fun x =>
    Nat.beq (pg 11 (mask 11) (HPD.S j) x) (pg 11 (mask 11) (HSD.S j) x)),
    allN 100 (fun x => Nat.beq (pg 11 (mask 11) (HPD.S j) (1100 + x))
      (pg 7 (mask 7) (HP.F j) x + 1100)))) = true := by quickRfl

theorem append_unpack {n m w v P Q R : Nat}
    (h1 : ∀ x < n, pg w (mask w) R x = pg w (mask w) P x)
    (h2 : ∀ x < m, pg w (mask w) R (n + x) = pg v (mask v) Q x + n) :
    unpack n w P ++ (unpack m v Q).map (· + n) = unpack (n + m) w R := by
  apply Array.ext
  · simp [unpack]
  · intro i hi1 hi2
    simp only [unpack, Array.getElem_append, Array.getElem_map, Array.getElem_ofFn,
      Array.size_ofFn]
    split_ifs with hlt
    · exact (h1 i hlt).symm
    · have hi : i < n + m := by simpa [unpack] using hi2
      have e := h2 (i - n) (by omega)
      rw [show n + (i - n) = i by omega] at e
      exact e.symm

theorem pair_eq {j : Nat} (hj : j < 2) {d : Array Nat} (hd : d = unpack 1100 11 (HSD.S j)) :
    d ++ (hs100Arr j).map (· + 1100) = unpack 1200 11 (HPD.S j) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec pairK j hj)
  rw [hd, hs100Arr_eq j (by omega)]
  exact append_unpack (n := 1100) (m := 100)
    (fun x hx => Nat.eq_of_beq_eq_true (allN_spec h1 x hx))
    (fun x hx => Nat.eq_of_beq_eq_true (allN_spec h2 x hx))

theorem pairA_eq : pairA = unpack 1200 11 (HPD.S 0) := pair_eq (by norm_num) HN2092.a_eq

theorem pairB_eq : pairB = unpack 1200 11 (HPD.S 1) := pair_eq (by norm_num) HN2092.b_eq

theorem o_get : (#[pairA, pairB] : Array (Array Nat)).size = 2 ∧
    ∀ j < 2, (#[pairA, pairB] : Array (Array Nat))[j]! = unpack 1200 11 (HPD.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · exact pairA_eq
  · exact pairB_eq

theorem bK : allN 4 (fun t => Nat.beq (pg 11 (mask 11) HPD.BP t)
    ((pairBase.map Fin.val).toArray[t]!)) = true := by quickRfl

theorem pair_ok : pairCheck = true :=
  chainCheck_of o_get (by decide +kernel) (by decide +kernel) (by simp only [dD, Array.toArray_toList])
    (by norm_num) (HN2089.base_of (by decide +kernel) bK) HPD.head HPD.hl (by decide +kernel) HPD.hs
    dPC (by decide +kernel)

end CertificateChecks.KernelSpor.HNPair

end
