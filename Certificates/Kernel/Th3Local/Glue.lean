module

public import Certificates.Kernel.Th3Local.Chk
public import Certificates.Kernel.ThCent.Consumers
public import CFSG.Certificates.Kernel.Th3Local.Sound

public section

namespace CertificateChecks.KernelTh3Local

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.Th.Spec CFSG.KC.ThCent CFSG.KC.Th3Local
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))


theorem mat_reg (r : ℕ) : 𝕄 (slpJ a b prog3 r) = pkMat (CFSG.KD.Th3Local.reg r) := by
  obtain ⟨hA, hB, -, hk⟩ := KernelThCent.fwd_mats
  unfold CFSG.KD.Th3Local.reg
  rw [pkMat_runPk hk _ (by decide +kernel) _ _ (pkMat_initPk hk a b hA hB),
    KernelThCent.slpJ_eq]
  rfl

theorem ord_reg {r p : ℕ} (hp : p.Prime) (hp64 : p < 64)
    (h : CFSG.KD.Th3Local.ordB r p = true) : orderOf (slpJ a b prog3 r) = p := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  unfold CFSG.KD.Th3Local.ordB at h
  rw [strictF_eq] at h
  exact ordPk_spec hk hp hp64 (mat_reg r) h

theorem comm_reg {r q : ℕ} (h : CFSG.KD.Th3Local.commB r q = true) :
    slpJ a b prog3 r * slpJ a b prog3 q = slpJ a b prog3 q * slpJ a b prog3 r := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  unfold CFSG.KD.Th3Local.commB at h
  rw [strictF_eq, strictF_eq] at h
  exact commPk_spec hk (mat_reg r) (mat_reg q) h

theorem th3_local :
    orderOf (slpJ a b prog3 11) = 3 ∧ orderOf (slpJ a b prog3 14) = 7 ∧
      orderOf (slpJ a b prog3 12) = 13 ∧
      slpJ a b prog3 11 * slpJ a b prog3 14 = slpJ a b prog3 14 * slpJ a b prog3 11 ∧
      slpJ a b prog3 11 * slpJ a b prog3 12 = slpJ a b prog3 12 * slpJ a b prog3 11 :=
  ⟨ord_reg (by norm_num) (by norm_num) CFSG.KD.Th3Local.ord11,
    ord_reg (by norm_num) (by norm_num) CFSG.KD.Th3Local.ord14,
    ord_reg (by norm_num) (by norm_num) CFSG.KD.Th3Local.ord12,
    comm_reg CFSG.KD.Th3Local.comm14, comm_reg CFSG.KD.Th3Local.comm12⟩

end CertificateChecks.KernelTh3Local

end
