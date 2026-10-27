module

public import CFSG.Certificates.Kernel.F42Sound
public import Certificates.Data.Kernel.F42Sq
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42 CFSG.EvenSmallLie.FFourTwo

theorem mg_eq (E i : ℕ) : Pc.mg cmF 25 E i = mgR cmK 25 E i := by rw [mgR_eq, cmK_eq_cmF]

theorem mw_eq (E w : ℕ) : Pc.mw cmF 25 E w = mwR (mgR cmK 25) E w := by
  rw [mwR_eq (mgR_eq cmK 25), cmK_eq_cmF]

theorem inv_eq (E : ℕ) : Pc.inv cmF 25 E = invG cmK 25 E := by rw [invG_eq, cmK_eq_cmF]

@[expose] noncomputable def preCenK : ℕ → Array ℕ
  | 0 => #[0]
  | k + 1 => (Pc.extend k (preCenK k)).filter fun q =>
      (List.range 25).all fun i =>
        mgR cmK 25 (mwR (mgR cmK 25) (mgR cmK 25 q i) (invG cmK 25 q)) i % 2 ^ (k + 2) == 0

theorem preCen_eq : ∀ k, Pc.preCen cmF 25 k = preCenK k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Pc.preCen, preCenK, ih]
    simp only [Pc.commGen, Pc.mul, mg_eq, mw_eq, inv_eq]

theorem small_ok : smallCheck = true := by
  simp only [smallCheck, mulU, weylU, Pc.mul, Pc.mulList, mg_eq, mw_eq]
  quickRfl

theorem wit_ok : witCheck = true := by
  delta witCheck witOK letterOK witProd commHU hOK hU conjU negU mulU invU Pc.mul Pc.mulList
  simp only [mg_eq, mw_eq, inv_eq]
  quickRfl

theorem cen_ok : cenCheck = true := by
  rw [cenCheck, preCen_eq]
  quickRfl

theorem wP_fields : (List.range 96).all (fun k => Nat.beq (fldW wP 5 k) (weylTab.getD k 0)) = true := by
  decide +kernel

theorem wP_blt : Nat.blt wP (Nat.pow 2 (Nat.mul 5 96)) = true := by quickRfl

set_option exponentiation.threshold 1000 in
theorem wP_eq (k : ℕ) : fldW wP 5 k = weylTab.getD k 0 := by
  by_cases hk : k < 96
  · exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 wP_fields k (List.mem_range.2 hk))
  · have h1 : weylTab.getD k 0 = 0 := by
      have hs : weylTab.size = 96 := by decide +kernel
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    have h2 : Nat.shiftRight wP (Nat.mul 5 k) = 0 := by
      change wP >>> (5 * k) = 0
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
      exact (Nat.blt_eq ▸ wP_blt : wP < 2 ^ (5 * 96)).trans_le
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [h1, fldW, h2]
    rfl

theorem conjR_eq (a x : ℕ) : conjR a x = conjU a x := by
  rw [conjR, conjU, mulR_eq, mg_eq]

theorem weylR_eq (a x : ℕ) : weylR a x = weylU a x := by
  simp only [weylR, weylU, Pc.mulList, bitsBelow, zPart, mg_eq, wP_eq]

theorem mvR_eq (d x : ℕ) : mvR d x = mv d x := by
  simp only [mvR, mv, conjR_eq, weylR_eq]

theorem mvOKR_eq (d x : ℕ) : mvOKR d x = mvOK d x := rfl

@[expose] noncomputable def chainOKK : ℕ → List ℕ → Bool
  | x, [] => r8.contains x
  | x, d :: l => mvOKR d x && chainOKK (mvR d x) l

theorem chainOK_eq : ∀ l x, chainOK x l = chainOKK x l := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons d l ih => intro x; simp only [chainOK, chainOKK, ih, mvR_eq, mvOKR_eq]

theorem chains_ok : chainsCheck = true := by
  simp only [chainsCheck, chainOK_eq]
  quickRfl

end CertificateChecks.KernelLC.F42

end
