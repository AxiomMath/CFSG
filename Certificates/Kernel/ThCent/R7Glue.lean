module

public import Certificates.Kernel.ThCent.LGlue
public import Certificates.Kernel.ThCent.R7C0
public import Certificates.Kernel.ThCent.R7C1
public import CFSG.Certificates.Kernel.ThCent.RankSound
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelThList

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.KC.ThCent CFSG.KD.ThCent.L CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThList
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative CFSG.KD
  CFSG.KD.ThCent

set_option maxRecDepth 100000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

#kc_forall_tree r7_all (fun k => CFSG.KD.ThCent.L.r7 k = true) 24 CFSG.KD.ThCent.L.r7_


theorem el7_mat (i : ℕ) (hi : i < L7.E.length) :
    𝕄 (el7 i) = pkMat (wordR ThS.c ThS.rm ThS.ONE V7 (L7.E[i]).1) := by
  have hw := words_of_map E7_words i hi
  unfold el7
  rw [← hw]
  exact mat_word mat_R7 (regsOK_spec E7_regs i hi).1

theorem th_rank7 :
    (∃ i < 1176, orderOf (el7 i) = 4) ∧
      ∀ i < 1176, el7 i * slpJ a b prog7 25 = slpJ a b prog7 25 * el7 i → el7 i ^ 7 = 1 := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have hy := mat_R7 25 (by decide)
  have hall := all_of_chunkOK _ L7.E 49 24 (by rw [E7_length]) fun k hk' => r7_all k hk'
  refine ⟨⟨153, by norm_num, ?_⟩, fun i hi hc => ?_⟩
  · have h153 : 153 < L7.E.length := by rw [E7_length]; norm_num
    have hw : (L7.E.getD 153 ([], [], 0)).1 = (L7.E[153]).1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h153, Option.getD_some]
    have h := ord4_ok
    unfold ord4 at h
    rw [hw] at h
    obtain ⟨h4, h2⟩ := ord4OK_sound hk h
    rw [← el7_mat 153 h153, ← mat_pow] at h4 h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord := orderOf_eq_prime_pow (p := 2) (n := 1) (x := el7 153)
      (fun e => h2 (by rw [pow_one] at e; rw [e, mat_one]))
      (mat_inj (by rw [mat_pow, mat_one, ← mat_pow]; exact h4))
    rw [hord]
    norm_num
  · have hiE : i < L7.E.length := by rw [E7_length]; exact hi
    rcases rank7OK_sound hk (hall i hiE) with h1 | h1
    · rw [← el7_mat i hiE, ← hy, ← mat_mul, ← mat_mul, hc] at h1
      exact absurd rfl h1
    · exact mat_inj (by rw [mat_pow, el7_mat i hiE, h1, mat_one])

end CertificateChecks.KernelThList

end
