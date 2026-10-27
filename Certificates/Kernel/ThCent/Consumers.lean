
module

public import Certificates.Kernel.ThCent.ConsumersBase

public import Certificates.Kernel.ThCent.Leaves
public import Certificates.Kernel.ThCent.Pin
public import CFSG.Certificates.Kernel.ThCent.PinSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace CertificateChecks.KernelThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec
  CFSG.KC.Th.Spec.FwdRel CFSG.SectionRank.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp CFSG.KD

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem slpJ_eq (g h : J) (prog : List Op) :
    slpJ g h prog = slpG g h prog := by
  have e : ∀ (R : ℕ → J) (op : Op), opJ R op = opG R op := by
    intro R op
    cases op <;> rfl
  unfold slpJ slpG
  have e2 : initJ g h = initG g h := rfl
  rw [e2]
  generalize initG g h = R
  induction prog generalizing R with
  | nil => rfl
  | cons op prog ih => rw [List.foldl_cons, List.foldl_cons, e, ih]

theorem fwd_mats : 𝕄 a = pkMat (ThS.RBf 1) ∧ 𝕄 b = pkMat (ThS.RBf 2) ∧
    𝕄 (b⁻¹ : J) = pkMat ThS.Bi ∧
    BigS.constsOK ThS.c ThS.rm thcFwdData.ThS_tm0 thcFwdData.ThS_tm1 thcFwdData.ThS_tm2
      thcFwdData.ThS_tm3 thcFwdData.ThS_tm4 thcFwdData.ThS_tm5 thcFwdData.ThS_tm6
      thcFwdData.ThS_tm7 thcFwdData.ThS_up thcFwdData.ThS_dg ThS.ONE = true := by
  obtain ⟨h1, h2, h3⟩ := hsw_th
  have hLA := seedA_eq.symm.trans thcFwd_hA
  have hLB := seedB_eq.symm.trans thcFwd_hB
  have ha : 𝕄 a = CFSG.Blueprint.NativeSporadic.decode 2 248 1
      (String.ofList thcFwdData.ThSeed_LA) := by
    rw [← hLA]
    rfl
  have hb : 𝕄 b = CFSG.Blueprint.NativeSporadic.decode 2 248 1
      (String.ofList thcFwdData.ThSeed_LB) := by
    rw [← hLB]
    rfl
  obtain ⟨-, -, -, -, hA, hB, hBi, hk⟩ :=
    CFSG.KC.Th.Spec.FwdExt.fwd_ext _ h1 h2 h3 thcFwdData thcFwd_chk a b ha hb
  rw [thcFwd_RBf] at hA hB
  rw [thcFwd_Bi] at hBi
  rw [thcFwd_c, thcFwd_rm, thcFwd_ONE] at hk
  exact ⟨hA, hB, hBi, hk⟩

theorem mat_zJ : 𝕄 ThCent.zJ = pkMat CFSG.KD.ThCent.W.Z3B := by
  obtain ⟨hA, hB, hBi, hk⟩ := fwd_mats
  have hA2 : pkMat (ThS.RBf 1) * pkMat (ThS.RBf 1) = 1 := by
    rw [← pkMat_mulB hk, Nat.eq_of_beq_eq_true CFSG.KD.ThCent.Pin.a2, pkMat_one hk]
  have hBi' : pkMat (ThS.RBf 2) * pkMat ThS.Bi = 1 := by
    rw [← hB, ← hBi]
    exact mat_mul_inv b
  have h1 := pkMat_wordZ hk a b hA hB hA2 hBi' (w := Native.abWord Native.x1Str)
    (by decide +kernel)
  have h2 := pkMat_wordZ hk a b hA hB hA2 hBi' (w := Native.abWord Native.x2Str)
    (by decide +kernel)
  have e := CFSG.KD.ThCent.Pin.z3B
  rw [strictF_eq] at e
  unfold ThCent.zJ ThCent.x1J ThCent.x2J
  rw [mat_pow, mat_mul, ← Nat.eq_of_beq_eq_true e, pkMat_powB hk _ _ _ (by norm_num),
    pkMat_mulB hk, h1, h2]

theorem mat_s3 :
    𝕄 (slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11) =
      pkMat CFSG.KD.ThCent.W.Z3A := by
  obtain ⟨hA, hB, -, hk⟩ := fwd_mats
  rw [← Nat.eq_of_beq_eq_true CFSG.KD.ThCent.Pin.s3A, pkMat_runPk hk _ (by decide +kernel) _ _
    (pkMat_initPk hk a b hA hB), slpJ_eq]
  rfl

theorem mat_z7 :
    𝕄 (slpJ a b CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative.prog7 24 *
      slpJ a b CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative.prog7 25 ^ 6) =
      pkMat CFSG.KD.ThCent.W.Z7 := by
  obtain ⟨hA, hB, -, hk⟩ := fwd_mats
  rw [← Nat.eq_of_beq_eq_true CFSG.KD.ThCent.Pin.z7, pkMat_runPk hk _ (by decide +kernel) _ _
    (pkMat_initPk hk a b hA hB), slpJ_eq, slpG, List.foldl_append]
  generalize List.foldl opG (initG a b)
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative.prog7 = R
  simp only [List.foldl_cons, List.foldl_nil, opG, Function.update_self,
    Function.update_of_ne (show (24 : ℕ) ≠ 43 by decide)]

variable (h : KernelFacts)
include h

theorem card_centralizer_zJ_le :
    Nat.card (Subgroup.centralizer ({ThCent.zJ} : Set J)) ≤ 472392 :=
  card_centralizer_z3B_le h _ mat_zJ

theorem card_centralizer_s3_le :
    Nat.card (Subgroup.centralizer
      ({slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11} : Set J)) ≤
        15921360 :=
  card_centralizer_z3A_le h _ mat_s3

theorem card_centralizer_x7y7_le :
    Nat.card (Subgroup.centralizer
      ({slpJ a b CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative.prog7 24 *
        slpJ a b CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative.prog7 25 ^ 6} :
          Set J)) ≤ 1176 :=
  card_centralizer_z7_le h _ mat_z7

end CertificateChecks.KernelThCent

end
