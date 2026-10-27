module

public import Certificates.Kernel.Sporadic.Suz.Text2306
public import Certificates.Kernel.Sporadic.SuzInv.Text1
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.SuzRecog.ChartTransferTests
meta import CFSG.Sporadic.SuzRecog.ChartTransferTests
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzQT CFSG.ComponentClassification.AS81.SuzB0.qText

#kmisc_hexflat CertificateChecks.KernelSpor.SuzQT CFSG.ComponentClassification.AS81.SuzB0.qText
  3 1782 11 1

namespace CertificateChecks.KernelSpor.SuzChart

open CFSG.Sporadic.SuzRecog.RigidL2 CFSG.Monster.B.Co2.Native

meta def ppM : Array (Array Nat) :=
  (Array.range 31).map fun i => bWordTab (chartWord.drop i)

meta def xM : Array (Array Nat) :=
  #[compA 1782 chartTab CFSG.ComponentClassification.AS81.SuzB0.tTab,
    compA 1782 CFSG.ComponentClassification.AS81.SuzB0.tTab chartTab]

end CertificateChecks.KernelSpor.SuzChart

#kmisc_packarrs CertificateChecks.KernelSpor.ChartPP CertificateChecks.KernelSpor.SuzChart.ppM 11

#kmisc_packarrs CertificateChecks.KernelSpor.ChartX CertificateChecks.KernelSpor.SuzChart.xM 11

namespace CertificateChecks.KernelSpor.SuzChart

open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.RigidL2 CFSG.Monster.B.Co2.Native CFSG.KS.Raw
open CFSG.KS.Prim
open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.SuzOddCore

@[expose] noncomputable def BL (k : Nat) : Nat := Bool.rec Suz2306.B1 Suz2306.B0 (Nat.beq k 0)

theorem steps : allN 30 (fun i =>
    compEqK 1782 11 (mask 11) (1782 * 11) (BL (chartWord.getD i 0)) (ChartPP (Nat.succ i))
      (ChartPP i)) = true := by
  quickRfl

theorem pp30 : Nat.beq (ChartPP 30) (pidn 1782 11) = true := by
  quickRfl

theorem letters : chartWord.all (fun k => decide (k < 2)) = true := by
  decide

theorem bL_eq {k : Nat} (hk : k < 2) : bLetterTab k = unpack 1782 11 (BL k) := by
  interval_cases k
  · exact Suz2306.b0Arr_eq
  · exact Suz2306.b1Arr_eq

theorem idA_eq : idA 1782 = unpack 1782 11 (pidn 1782 11) :=
  (idK_sound (by quickRfl)).symm

theorem fold_aux : ∀ j ≤ 30, (chartWord.drop (30 - j)).foldr
    (fun l t => compA 1782 (bLetterTab l) t) (idA 1782) = unpack 1782 11 (ChartPP (30 - j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [Nat.eq_of_beq_eq_true pp30, ← idA_eq]
    rfl
  | succ j ih =>
    intro hj
    have hk' : 30 - (j + 1) < 30 := by omega
    have hk30 : 30 - (j + 1) < chartWord.length := by simpa [chartWord] using hk'
    have hs : 30 - (j + 1) + 1 = 30 - j := by omega
    have hd : chartWord.drop (30 - (j + 1)) =
        chartWord.getD (30 - (j + 1)) 0 :: chartWord.drop (30 - j) := by
      rw [List.getD_eq_getElem _ _ hk30, List.drop_eq_getElem_cons hk30, hs]
    have hl : chartWord.getD (30 - (j + 1)) 0 < 2 := by
      have := List.all_eq_true.1 letters (chartWord.getD (30 - (j + 1)) 0)
        (by rw [List.getD_eq_getElem _ _ hk30]; exact List.getElem_mem hk30)
      simpa using this
    have hst := allN_spec steps (30 - (j + 1)) hk'
    rw [Nat.succ_eq_add_one, hs] at hst
    rw [hd, List.foldr_cons, ih (by omega), bL_eq hl]
    exact compEqK_sound hst

theorem chartTab_eq : chartTab = unpack 1782 11 (ChartPP 0) := fold_aux 30 (by norm_num)

theorem tTab_eq : CFSG.ComponentClassification.AS81.SuzB0.tTab = unpack 1782 11 (SuzInvT1.F 0) :=
  CertificateChecks.KernelSpor.SuzInv.run_eq1 (k := 0) (by norm_num)

theorem w0Tab_eq : w0Tab = compA 1782 (idA 1782) (unpack 1782 11 (SuzQT.F 0)) := by
  have hq := CFSG.KC.Misc.HexFlat.hexTable_sound SuzQT.all 0 (by norm_num)
  rw [← SuzQT.eq] at hq
  simp only [Nat.mul_zero] at hq
  unfold w0Tab CFSG.ComponentClassification.AS81.SuzB0.qProds
  rw [getElem!_pos _ 1 (by simp), Array.getElem_ofFn]
  unfold CFSG.ComponentClassification.AS81.SuzB0.qProd CFSG.ComponentClassification.AS81.SuzB0.qArr
  simp [List.range_succ, Nat.testBit, hq, CFSG.PSL3Four.Native.idTab, idA]

theorem e1 : compEqK 1782 11 (mask 11) (1782 * 11) (ChartPP 0) (SuzInvT1.F 0) (ChartX 0) = true := by
  quickRfl
theorem e2 : compEqK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) (SuzQT.F 0) (SuzQT.F 0) = true := by
  quickRfl
theorem e3 : compEqK 1782 11 (mask 11) (1782 * 11) (SuzQT.F 0) (ChartPP 0) (ChartX 0) = true := by
  quickRfl
theorem e4 : compEqK 1782 11 (mask 11) (1782 * 11) (SuzInvT1.F 0) (ChartPP 0) (ChartX 1) = true := by
  quickRfl
theorem e5 : compEqK 1782 11 (mask 11) (1782 * 11) (ChartPP 0) (SuzQT.F 0) (ChartX 1) = true := by
  quickRfl

theorem facts15111 : chartSwapOK = true := by
  have hw : w0Tab = unpack 1782 11 (SuzQT.F 0) := by
    rw [w0Tab_eq, idA_eq, compEqK_sound e2]
  unfold chartSwapOK
  rw [letters, chartTab_eq, tTab_eq, hw, compEqK_sound e1, compEqK_sound e3, compEqK_sound e4,
    compEqK_sound e5, eqK_sound (n := 1782) (w := 11) (Nat.beq_refl (ChartX 0)),
    eqK_sound (n := 1782) (w := 11) (Nat.beq_refl (ChartX 1))]
  rfl

end CertificateChecks.KernelSpor.SuzChart

end
