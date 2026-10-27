module

public import Certificates.Kernel.Misc.Perm.HSMcL
public import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HSMcL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.PairCount
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.Misc.Clos (allN_iff)

theorem kappa_inj_proved : Function.Injective hs100Kappa := by
  intro x y hxy
  have key : ∀ x y : Fin 3850, hs100Kappa x = hs100Kappa y →
      (hs100K1 x : ℕ) ≤ hs100K1 y := by
    intro x y h
    have hm : hs100K1 y ∈ hs100Kappa x := by rw [h]; simp [hs100Kappa]
    simp only [hs100Kappa, Finset.mem_insert, Finset.mem_singleton] at hm
    have hl := k1_lt x.2
    rw [← K1_val, ← K2_val] at hl
    rcases hm with hm | hm
    · rw [hm]
    · rw [hm]
      omega
  have h1 : (hs100K1 x : ℕ) = hs100K1 y := le_antisymm (key x y hxy) (key y x hxy.symm)
  have h2 : (hs100K2 x : ℕ) = hs100K2 y := by
    have hm : hs100K2 x ∈ hs100Kappa y := by rw [← hxy]; simp [hs100Kappa]
    simp only [hs100Kappa, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · have := k1_lt x.2
      rw [← K1_val, ← K2_val] at this
      rw [hm] at this
      omega
    · rw [hm]
  rw [K1_val, K1_val] at h1
  rw [K2_val, K2_val] at h2
  exact Fin.ext (CFSG.KC.Misc.Clos.sort_distinct_proved sorted x x.2 y y.2 (by
    change Nat.add (Nat.mul 100 _) _ = Nat.add (Nat.mul 100 _) _
    rw [h1, h2]))

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Schreier in
open Certificates in
theorem facts_proved : (

    rawChainOK 100 (hs100StrongArrs.extract 0 2) hs100StrongArrs hs100BaseArr hs100Words 1 =
        true ∧
      rawOrbitSizes 100 hs100StrongArrs hs100BaseArr = [100, 77, 60, 12, 8] ∧
      eqA 100 (compA 100 (hs100Arr 15) (hs100Arr 15)) (idA 100) = true ∧
      isInvA 100 (hs100Arr 15) (invCand 100 (hs100Arr 15)) = true ∧
      allLt 100 (fun x => x == 0 || (List.range 15).any fun j =>
        (hs100StrongArrs[j]!)[0]! == 0 && (hs100StrongArrs[j]!)[x]! != x) = true
)
    ∧ (

    rawChainOK 100 (hs100RArrs.extract 0 3) hs100RArrs hs100RBaseArr hs100RWords 1 = true ∧
      rawOrbitSizes 100 hs100RArrs hs100RBaseArr = [100, 77, 16, 45, 8, 2] ∧
      eqA 100 hs100RArrs[0]! (hs100Arr 0) = true ∧ eqA 100 hs100RArrs[1]! (hs100Arr 1) = true ∧
      eqA 100 hs100RArrs[2]! (hs100Arr 15) = true
)
    ∧ (

    rawChainOK 275 (mcl275RArrs.extract 0 3) mcl275RArrs mcl275RBaseArr mcl275RWords 1 = true ∧
      rawOrbitSizes 275 mcl275RArrs mcl275RBaseArr = [275, 112, 81, 45, 16] ∧
      eqA 275 mcl275RArrs[0]! mclStrongArrs[0]! = true ∧
      eqA 275 mcl275RArrs[1]! mclStrongArrs[1]! = true ∧
      eqA 275 mcl275RArrs[2]! (CFSG.Sporadic.SmallOddCore.Native.natArr
        CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true ∧
      isInvA 275 (CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl)
        (invCand 275 (CFSG.Sporadic.SmallOddCore.Native.natArr
          CFSG.Sporadic.SmallOddCore.mclOuterTbl)) = true
)
    ∧ (

    allLt 3850 (fun x => decide (hs100Kappa1[x]! < hs100Kappa2[x]!) &&
        decide (hs100Kappa2[x]! < 100)) = true ∧
      hs100KappaEquiv hsStrongArrs[0]! (hs100Arr 0) = true ∧
      hs100KappaEquiv hsStrongArrs[1]! (hs100Arr 1) = true
)
    ∧ (

    Function.Injective hs100Kappa ∧ (∀ x, (hs100Kappa x).card = 2) ∧ hs100Kappa 0 = {0, 78} ∧
      ∀ i : Fin 100, (Finset.univ.filter fun x => i ∈ hs100Kappa x).card = 77
) :=
  ⟨⟨chain1, orbits1, sq15, inv15, moved⟩,
    ⟨chain2, orbits2, r_eq 0 0 (by norm_num) (by norm_num) (by quickRfl),
      r_eq 1 1 (by norm_num) (by norm_num) (by quickRfl),
      r_eq 2 15 (by norm_num) (by norm_num) (by quickRfl)⟩,
    ⟨chain3, orbits3, m_eq 0 (by norm_num) (by quickRfl), m_eq 1 (by norm_num) (by quickRfl),
      m_outer, m_outer_inv⟩,
    ⟨kappa_order, equiv0, equiv1⟩,
    ⟨kappa_inj_proved, kappa_card, kappa_zero, kappa_count⟩⟩

end CertificateChecks.KernelMisc.HSMcL

end
