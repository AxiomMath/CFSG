
module

public import Certificates.Kernel.OmegaEight.SB3872
public import Certificates.Kernel.OmegaEight.SB3873Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLevel1Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872

@[expose] noncomputable def WK (k m e : ℕ) : ℕ := wLit.getD (16 * k + m - 16) 0 / 2 ^ (16 * e) % 2 ^ 16

@[expose] noncomputable def LK (k a : ℕ) : ℕ := lLit.getD k 0 / 2 ^ (16 * a) % 2 ^ 16

@[expose] noncomputable def FK (k m x : ℕ) : ℕ := mulK (WK k m (nfEK x)) (LK k (nfAK x))

@[expose] noncomputable def wOK (k m : ℕ) : Bool :=
  (List.range 128).all fun e => WK k m e ==
    wprodN mulK 7 (fun l => mulK ((sH.getD k []).getD l 0) (linK (((sLeaves k).getD m []).getD l 0))) e

@[expose] noncomputable def lOK (k : ℕ) : Bool :=
  (List.range 512).all fun a => LK k a == linK (xorBits 9 (fun i => (sP.getD k []).getD i 0) a)

theorem nf_lt {c : ℕ} (hc : c < 65536) : nfEK c < 128 ∧ nfAK c < 512 := by
  have h := sCheck1_parts.2.1 c hc
  simp only [sAutData, sNfTab_get] at h
  exact ⟨h.1, h.2.1⟩

theorem nfEK_ge {c : ℕ} (hc : ¬ c < 65536) : nfEK c = 0 := by
  rw [nfEK, nfEG, nIf_blt, ite_eq_right hc]

theorem nfAK_ge {c : ℕ} (hc : ¬ c < 65536) : nfAK c = 0 := by
  rw [nfAK, nfAG, nIf_blt, ite_eq_right hc]

theorem sFTab_eq {k m : ℕ} (hw : wOK k m = true) (hl : lOK k = true) :
    (fun c => (sFTab k m)[c]!) = FK k m := by
  unfold wOK at hw
  unfold lOK at hl
  rw [List.all_eq_true] at hw hl
  have hw' : ∀ e < 128, WK k m e = wprodN mulK 7
      (fun l => mulK ((sH.getD k []).getD l 0) (linK (((sLeaves k).getD m []).getD l 0))) e :=
    fun e he => beq_iff_eq.1 (hw e (List.mem_range.2 he))
  have hl' : ∀ a < 512, LK k a = linK (xorBits 9 (fun i => (sP.getD k []).getD i 0) a) :=
    fun a ha => beq_iff_eq.1 (hl a (List.mem_range.2 ha))
  funext c
  by_cases hc : c < 65536
  · rw [sFTab_get k m hc, sFm, AutData.F, sMul_eqK, FK, hw' _ (nf_lt hc).1, hl' _ (nf_lt hc).2]
    simp only [sAutData, sNfTab_get, a9K_lin, ys_fun, AutData.Pk]
    rfl
  · rw [getElem!_neg _ c (by simpa [sFTab] using hc), FK, nfEK_ge hc, nfAK_ge hc,
      hw' 0 (by norm_num), hl' 0 (by norm_num), ← sMul_eqK]
    simp only [wprodN, Nat.zero_testBit, Bool.false_eq_true, ite_false, List.foldl_fixed]
    have h0 : linK (xorBits 9 (fun i => (sP.getD k []).getD i 0) 0) = 0 := by
      have hx : xorBits 9 (fun i => (sP.getD k []).getD i 0) 0 = 0 := by
        simp [xorBits, Nat.zero_testBit]
      rw [hx]
      decide +kernel
    rw [h0, sMul_zero_zero]
    rfl

end CertificateChecks.KernelO8.SB3873

end
