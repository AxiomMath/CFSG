module

public import Certificates.Kernel.OmegaEight.SB3880VD
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Enum
public import Certificates.Kernel.OmegaEight.SB3872
public import Certificates.Kernel.OmegaEight.SB3873Data
public import Certificates.Kernel.OmegaEight.SB3884Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def vSK (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 65536),
    fld(vSRow (Nat.shiftRight c (nat_lit 7)), Nat.mul (nat_lit 9) (Nat.land c (nat_lit 127)),
      nat_lit 511), nat_lit 0)

@[expose] def vSArr : Array ℕ :=
  Array.ofFn (n := 65536) fun c => vSRow (c.val / 128) / 2 ^ (9 * (c.val % 128)) % 2 ^ 9

theorem vSArr_get (c : ℕ) : vSArr[c]! = vSK c := by
  rw [vSK, nIf_blt]
  by_cases hc : c < 65536
  · rw [ite_eq_left hc, getElem!_pos vSArr _ (by simpa [vSArr] using hc)]
    simp only [vSArr, Array.getElem_ofFn, l127, l511, shr_eq, Nat.mul_eq]
    rfl
  · rw [ite_eq_right hc, getElem!_neg vSArr _ (by simpa [vSArr] using hc)]
    rfl

@[expose] noncomputable def vecK (c : Nat) : Nat :=
  if c < 65536 then vSK c else if c < 131072 then Nat.xor (vSK (c - 65536)) 512 else 0

theorem vec_get (c : ℕ) : (t1Vec vSArr)[c]! = vecK c := by
  unfold t1Vec vecK
  by_cases hc : c < 131072
  · rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]
    dsimp only
    by_cases hcS : c < 65536
    · rw [ite_eq_left hcS, ite_eq_left hcS, vSArr_get]
    · rw [ite_eq_right hcS, ite_eq_right hcS, ite_eq_left hc, vSArr_get]
      rfl
  · rw [getElem!_neg _ c (by simpa using hc), ite_eq_right (by omega), ite_eq_right hc]
    rfl

@[expose] noncomputable def FDK (k m x : ℕ) : ℕ :=
  mulK (wprodN mulK 7
      (fun l => mulK ((sH.getD k []).getD l 0) (linK (((sLeaves k).getD m []).getD l 0)))
      (nfEK x))
    (linK (xorBits 9 (fun i => (sP.getD k []).getD i 0) (nfAK x)))

theorem sFm_eqD (k m : ℕ) : sFm k m = FDK k m := by
  funext c
  rw [sFm, AutData.F, sMul_eqK, FDK]
  simp only [sAutData, sNfTab_get, a9K_lin, ys_fun, AutData.Pk]
  rfl

theorem cb_eq (l i : ℕ) : sAutData.cb l i =
    coK (cconj mulK invK (sPc.getD l 0) (linK (2 ^ i))) := by
  simp only [sAutData, sConj, a9CoTab_get, a9LinTab_get, sMul_eqK, sInv_eqK]

end CertificateChecks.KernelO8.SB3880

end
