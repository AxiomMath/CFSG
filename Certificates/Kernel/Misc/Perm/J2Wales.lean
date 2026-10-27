module

public import Certificates.Kernel.Misc.Perm.J2Rel
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WJ2Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2Fam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec14.Wales1411W.ModelJ2
open CertificateChecks.KernelMisc.J2C3 (cm I)

@[expose] noncomputable def GWW (i j l : ℕ) : ℕ :=
  [WG (2 * i), WG (2 * i + 1), WG (2 * j), WG (2 * j + 1)].getD l 0

theorem rGWW {i j : ℕ} (hi : i < 3) (hj : j < 3) : ∀ l < 4, R (et2GensWW i j)[l]! (GWW i j l) := by
  unfold et2GensWW
  exact R.arr4 (rwg0 hi) (rwg1 hi) (rwg0 hj) (rwg1 hj)

@[expose] noncomputable def nFactsK (i j c q : ℕ) : Bool :=
  memE0K (cm q (cm J2C3.Z (iv q))) && memE0K (cm q (cm J2C3.X (iv q))) &&
    memWK j (cm q (cm (WG (2 * i)) (iv q))) && memWK j (cm q (cm (WG (2 * i + 1)) (iv q))) &&
    memWK i (cm (iv q) (cm (WG (2 * j)) q)) && memWK i (cm (iv q) (cm (WG (2 * j + 1)) q)) &&
    memVkK c (cm q (cm (VK c 1) (iv q))) && memVkK c (cm q (cm (VK c 2) (iv q))) &&
    memVkK c (cm (iv q) (cm (VK c 1) q)) && memVkK c (cm (iv q) (cm (VK c 2) q))

theorem nFacts_eq {i j c : ℕ} (hi : i < 3) (hj : j < 3) (hc : c < 3) {n : Array ℕ} {q : ℕ}
    (hn : R n q) : et2NFacts i j c n = nFactsK i j c q := by
  unfold et2NFacts nFactsK
  rw [hn.valid, Bool.true_and, (hn.conj rZ).memE0, (hn.conj rX).memE0,
    (hn.conj (rwg0 hi)).memW hj, (hn.conj (rwg1 hi)).memW hj,
    (hn.conjInv (rwg0 hj)).memW hi, (hn.conjInv (rwg1 hj)).memW hi,
    (hn.conj (rVK hc 1)).memVk hc, (hn.conj (rVK hc 2)).memVk hc,
    (hn.conjInv (rVK hc 1)).memVk hc, (hn.conjInv (rVK hc 2)).memVk hc]

@[expose] noncomputable def nOKK (i j c : ℕ) (w : List ℕ) : Bool :=
  w.all (· < 4) && nFactsK i j c (w.foldr (fun l q => cm (GWW i j l) q) I)

theorem nOK_eq {i j c : ℕ} (hi : i < 3) (hj : j < 3) (hc : c < 3) (w : List ℕ) :
    et2NOK i j c w = nOKK i j c w := by
  unfold et2NOK nOKK et2Word
  cases hw : w.all (· < 4)
  · rfl
  · rw [nFacts_eq hi hj hc (R.foldr (rGWW hi hj) w hw)]

theorem chkN_K : et2ChkN = true := by
  have hK : et2NPairs.all (fun p => nOKK p.1 p.2 ((8 - p.1 - p.2) % 3) (et2NWord p.1 p.2)) =
      true := by quickRfl
  unfold et2ChkN
  rw [List.all_eq_true] at hK ⊢
  intro p hp
  have h3 : p.1 < 3 ∧ p.2 < 3 := by
    simp only [et2NPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  rw [nOK_eq h3.1 h3.2 (Nat.mod_lt _ (by norm_num))]
  exact hK p hp

@[expose] noncomputable def yWVK (i : ℕ) (w : List ℕ) : Bool :=
  w.all (· < 4) && Nat.beq J2C3.Y (w.foldr (fun l q => cm (GWV i l) q) I)

theorem yWV_eq {i : ℕ} (hi : i < 3) (w : List ℕ) :
    (w.all (· < 4) && eqA 315 yArr (et2Word (et2GensWV i) w)) = yWVK i w := by
  unfold yWVK et2Word et2GensWV
  cases hw : w.all (· < 4)
  · rfl
  · rw [rY.eq (R.foldr (R.wv hi) w hw)]

theorem yWV_K : et2YWV = true := by
  have hK : [0, 1, 2].all (fun i => yWVK i (et2YWords.getD i [])) = true := by quickRfl
  unfold et2YWV
  rw [List.all_eq_true] at hK ⊢
  intro i hi
  have h3 : i < 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  rw [yWV_eq h3]
  exact hK i hi

theorem yVV_K : et2YVV = true := by
  unfold et2YVV et2Word et2GensVV
  rw [rY.eq (R.foldr R.vk6 et2YVWord (by quickRfl))]
  quickRfl

theorem wales_K : et2YWV = true ∧ et2YVV = true ∧ et2ChkN = true := ⟨yWV_K, yVV_K, chkN_K⟩

end CertificateChecks.KernelMisc.J2Fam

end
