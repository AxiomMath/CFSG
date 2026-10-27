module

public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor

@[expose] noncomputable def G (k : Nat) : Nat := Fi22CGT.F k

@[expose] noncomputable def GI (k : Nat) : Nat := Fi22X.inv (Fi22CGT.F k)

@[expose] noncomputable def W (wd : List Int) : Nat :=
  wordK 3510 12 (mask 12) (pidn 3510 12) G GI wd

theorem permG : allN 2 (fun k => permOK 3510 12 (mask 12) (3510 * 12) (G k) (GI k)) = true := by
  quickRfl

theorem cnG : allN 2 (fun k => bAnd(Fi22X.cn (G k), Fi22X.cn (GI k))) = true := by quickRfl

theorem szOK' : szOK 3510 12 = true := by quickRfl

theorem idOK : idK 3510 12 (mask 12) = true := by quickRfl

theorem cnId : Fi22X.cn (pidn 3510 12) = true := by quickRfl

theorem gen_eq {k : Nat} (hk : k < 2) : fi22ChainGen k = unpack 3510 12 (G k) := Fi22G.gen_eq hk

theorem gen_cn {k : Nat} (hk : k < 2) : Fi22X.cn (G k) = true ∧ Fi22X.cn (GI k) = true :=
  (bAnd_iff _ _).1 (allN_spec cnG k hk)

theorem genInv_eq {k : Nat} (hk : k < 2) :
    invCand 3510 (fi22ChainGen k) = unpack 3510 12 (GI k) := by
  rw [gen_eq hk]
  exact (invEqK_sound (allN_spec permG k hk)).1

theorem wordS_eq {S : Array (Array Nat)} {PS PSI : Nat → Nat}
    (hS : S.size = 2 ∧ ∀ j < 2, S[j]! = unpack 3510 12 (PS j))
    (hp : allN 2 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (PS j) (PSI j)) = true)
    {wd : List Int} (hl : lettersK 2 wd = true) :
    wordA 3510 S (rawInvs 3510 S) wd =
      unpack 3510 12 (wordK 3510 12 (mask 12) (pidn 3510 12) PS PSI wd) := by
  refine (wordEqK_sound hS hp ?_).1
  rw [wordEqK]
  simp only [bAnd_iff, szOK', hl, true_and]
  exact Nat.beq_refl _

theorem word_eq {S : Array (Array Nat)} (hS : S.size = 2 ∧ ∀ j < 2, S[j]! = unpack 3510 12 (G j))
    {wd : List Int} (hl : lettersK 2 wd = true) :
    wordA 3510 S (rawInvs 3510 S) wd = unpack 3510 12 (W wd) :=
  wordS_eq hS permG hl

theorem orig_bind : fi22OrigArrs.size = 2 ∧ ∀ j < 2, fi22OrigArrs[j]! = unpack 3510 12 (G j) := by
  refine ⟨by simp [fi22OrigArrs], fun j hj => ?_⟩
  rw [← gen_eq hj, getElem!_pos _ j (by simpa [fi22OrigArrs] using hj)]
  simp [fi22OrigArrs]

theorem get_eq {P : Nat} (hP : Nat.shiftRight P (3510 * 12) = 0) (i : Nat) :
    (unpack 3510 12 P)[i]! = pg 12 (mask 12) P i := by
  by_cases hi : i < 3510
  · rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  · rw [getElem!_neg _ i (by simpa [unpack] using hi)]
    have hP' : P >>> (3510 * 12) = 0 := hP
    have hlt : P < 2 ^ (3510 * 12) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hP'
      rcases hP' with h | h
      · exact absurd h (by positivity)
      · exact h
    have hle : 2 ^ (3510 * 12) ≤ 2 ^ (12 * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 : P >>> (12 * i) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (lt_of_lt_of_le hlt hle)
    change 0 = (P >>> (12 * i)) &&& mask 12
    rw [h0, Nat.zero_and]

theorem get_eq_of_cn {P : Nat} (h : Fi22X.cn P = true) (i : Nat) :
    (unpack 3510 12 P)[i]! = pg 12 (mask 12) P i :=
  get_eq (Fi22X.hi_of h) i

end CertificateChecks.KernelSpor.Fi22W

end
