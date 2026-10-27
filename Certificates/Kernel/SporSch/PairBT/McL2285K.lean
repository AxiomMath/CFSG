module

public import Certificates.Kernel.SporSch.PairBT.McL2285
public import CFSG.Certificates.Kernel.SporSch.McLSylowProof

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McL2285K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Sporadic.Schreier.PairMcL CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.McLSylChk

theorem base_nodup : CFSG.Sporadic.Schreier.PairMcL.baseArr.toList.Nodup := by decide

private theorem count_eq {N : Nat} (h : 22275 * N * 11 = 898128000 * 22) : N = 80640 := by
  omega

theorem facts2285 :
    countPair PairMcL.bs 5 PairMcL.wA CFSG.Sporadic.SmallOddCore.mclWConds PairMcL.blocks =
      80640 := by
  have hN : ¬11 ^ 2 ∣ ordK PMcL.LR 5 := by
    rw [ord]
    decide
  have h := pair11_proved sz McL2285.chainS base_nodup (by decide)
    (allN_spec PMcLCheck.perm 0 (by decide)) (allN_spec PMcLCheck.perm 1 (by decide)) cA oA hN
    (bs := bs) (by decide) (groups := groups) (by decide) pZ pG cZ cG sZ sG oZ rel bZZ bZZi
    (d := McLCK.getD 0 clsD0) McL2285.clsOK (Nat.eq_of_beq_eq_true McL2285.hR0)
    (rest := McLBT.wConds.tail) (by decide)
    (Nat.le_of_ble_eq_true McL2285.lens.1) (Nat.le_of_ble_eq_true McL2285.lens.2)
    McLSylZ3.h0_0 McLSylZ3.h1_0
  rw [ord, Nat.eq_of_beq_eq_true McL2285.dc0, Nat.eq_of_beq_eq_true McL2285.rows] at h
  have e : CFSG.Sporadic.SmallOddCore.mclWConds = McLBT.wConds := rfl
  rw [PMcLCheck.wA_eq, e]
  have e2 : (([false, true], 11) :: McLBT.wConds.tail) = McLBT.wConds := rfl
  have e3 : blocksOf 275 (CFSG.Certificates.Native.rawLevels 275 mclStrongArrs PairMcL.baseArr)
      groups = blocks := rfl
  rw [e2, e3] at h
  exact count_eq h

end CertificateChecks.KernelSporSch.McL2285K

end
