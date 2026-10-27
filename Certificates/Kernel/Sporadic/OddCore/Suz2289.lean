module

public import Certificates.Kernel.Sporadic.OddCore.SuzCert
public import Certificates.Kernel.Sporadic.OddCore.SuzRelabel
public import Certificates.Kernel.Sporadic.Suz.Text2306
public import CFSG.Certificates.Kernel.Spor.MtxHSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
meta import CFSG.Sporadic.SuzOddCore.Arrays
import all CFSG.Sporadic.SuzOddCore.Arrays
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def smallInvM : Array (Array Nat) :=
  (List.range 14).toArray.map fun k => CFSG.Monster.B.Co2.Native.invCand 1782 (smallArr k)

meta def mtxInvM : Array (Array Nat) :=
  #[b0Arr, b1Arr, vArr].map (CFSG.Monster.B.Co2.Native.invCand 1782)

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzSmallI CertificateChecks.KernelSpor.OddCore.smallInvM 11

#kmisc_packarrs CertificateChecks.KernelSpor.SuzMtxI CertificateChecks.KernelSpor.OddCore.mtxInvM 11

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.Row CFSG.KC.MtxH CertificateChecks.KernelSpor.Suz2306

theorem permOK_unpack {n w p r : Nat} (h : invEqK n w (mask w) (n * w) p r = true) :
    CFSG.Sporadic.SuzOddCore.permOK n (unpack n w p) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound h
  unfold CFSG.Sporadic.SuzOddCore.permOK
  rw [h1, h2]
  simp [unpack]

theorem permOK_rows {n w o o' : Nat} {F G : Nat → Nat} (h : rpermK n w (mask w) F o G o' = true) :
    CFSG.Sporadic.SuzOddCore.permOK n (rowArr n w F o) = true := by
  obtain ⟨h1, h2⟩ := rpermK_sound h
  unfold CFSG.Sporadic.SuzOddCore.permOK
  rw [h1, h2]
  simp [size_rowArr]

theorem small_perms : allN 14 (fun k =>
    invEqK 1782 11 (mask 11) (1782 * 11) (SuzSmallT.F k) (SuzSmallI k)) = true := by
  quickRfl

theorem mtx_perms : bAnd(invEqK 1782 11 (mask 11) (1782 * 11) B0 (SuzMtxI 0),
    bAnd(invEqK 1782 11 (mask 11) (1782 * 11) B1 (SuzMtxI 1),
      invEqK 1782 11 (mask 11) (1782 * 11) V (SuzMtxI 2))) = true := by
  quickRfl

theorem hdrB0 : mtxHK 1782 11 B0 12 1 1782 1 SuzB0T.chars = true := by
  quickRfl

theorem hdrB1 : mtxHK 1782 11 B1 12 1 1782 1 SuzB1T.chars = true := by
  quickRfl

theorem hdrV : mtxHK 1782 11 V 12 1 1782 1 SuzVT.chars = true := by
  quickRfl

theorem gens01 : bAnd(Nat.beq (SuzSmallT.F 0) B0, Nat.beq (SuzSmallT.F 1) B1) = true := by
  quickRfl

theorem derivs : derivsOK 2 certDerivs = true ∧ derivsOK 2 smallDerivs = true := by
  decide +kernel

theorem arrays :
    (∀ k < 12, permOK 22880 (certArr k) = true) ∧ (∀ k < 14, permOK 1782 (smallArr k) = true) ∧
      mtxHeader suzP1782M1Text = [12, 1, 1782, 1] ∧ (mtxImages suzP1782M1Text).length = 1782 ∧
      mtxHeader suzP1782M2Text = [12, 1, 1782, 1] ∧ (mtxImages suzP1782M2Text).length = 1782 ∧
      mtxHeader suzd2P1782M1Text = [12, 1, 1782, 1] ∧ (mtxImages suzd2P1782M1Text).length = 1782 ∧
      permOK 1782 b0Arr = true ∧ permOK 1782 b1Arr = true ∧ permOK 1782 vArr = true ∧
      permOK 22880 relabelArr = true ∧
      derivsOK 2 certDerivs = true ∧ derivsOK 2 smallDerivs = true ∧
      smallArr 0 = b0Arr ∧ smallArr 1 = b1Arr := by
  obtain ⟨p0, p1, pv⟩ := (by simpa only [bAnd_iff] using mtx_perms :
    invEqK 1782 11 (mask 11) (1782 * 11) B0 (SuzMtxI 0) = true ∧
      invEqK 1782 11 (mask 11) (1782 * 11) B1 (SuzMtxI 1) = true ∧
      invEqK 1782 11 (mask 11) (1782 * 11) V (SuzMtxI 2) = true)
  obtain ⟨g0, g1⟩ := (by simpa only [bAnd_iff] using gens01 :
    Nat.beq (SuzSmallT.F 0) B0 = true ∧ Nat.beq (SuzSmallT.F 1) B1 = true)
  have h0 := mtxHK_sound hdrB0
  have h1 := mtxHK_sound hdrB1
  have hv := mtxHK_sound hdrV
  rw [← SuzB0T.eq] at h0
  rw [← SuzB1T.eq] at h1
  rw [← SuzVT.eq] at hv
  refine ⟨fun k hk => ?_, fun k hk => ?_, h0.1, h0.2.1, h1.1, h1.2.1, hv.1, hv.2.1, ?_, ?_, ?_, ?_,
    derivs.1, derivs.2, ?_, ?_⟩
  · rw [certArr_eq hk]
    exact permOK_rows (allN_spec cert_perms k hk)
  · rw [smallArr_eq hk]
    exact permOK_unpack (allN_spec small_perms k hk)
  · rw [b0Arr_eq]
    exact permOK_unpack p0
  · rw [b1Arr_eq]
    exact permOK_unpack p1
  · rw [vArr_eq]
    exact permOK_unpack pv
  · rw [relabelArr_eq]
    exact permOK_rows relabel_perm
  · rw [smallArr_eq (by omega), b0Arr_eq, Nat.eq_of_beq_eq_true g0]
  · rw [smallArr_eq (by omega), b1Arr_eq, Nat.eq_of_beq_eq_true g1]

theorem decoders : b0Arr = mtxArr suzP1782M1Text ∧ b1Arr = mtxArr suzP1782M2Text ∧
    vArr = mtxArr suzd2P1782M1Text ∧
    (∀ k < 12, certArr k = hexTable 4 22880 (22880 * k) certChainText) ∧
    (∀ k < 14, smallArr k = hexTable 3 1782 (1782 * k) smallChainText) :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end CertificateChecks.KernelSpor.OddCore

end
