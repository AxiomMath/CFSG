module

public import Certificates.Kernel.R148Dc.J2CData
public import Certificates.Kernel.Misc.Perm.J2Mult5
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BJ2V
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.R148Dc.J2CData
public import CFSG.Sporadic.Co1Block.TwoBTri

set_option maxRecDepth 400000

#ks_perm CFSG.KD.R148Dc.J2C.CP 9 CFSG.KD.R148Dc.J2C.cArr

public section

namespace CFSG.KD.R148Dc.J2C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ xJ zJ okA eltOf rep_eltOf)
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 (tJ)
open CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2

theorem hc : cArr = unpack 315 9 CP := arrBind_sound (by quickRfl)

theorem okc : okA cArr = true :=
  CertificateChecks.KernelMisc.J2M5.okA_of hc (by quickRfl) (by quickRfl) (by quickRfl)

@[expose] def cc : ℕ := pk cArr.toList

theorem okL_c : okL cArr = true := by decide +kernel

theorem cx_ok : eqOn (fun p => ev cc (ev cx p)) (fun p => ev cx (ev cz (ev cc p))) = true := by
  decide +kernel

theorem cz_ok : eqOn (fun p => ev cc (ev cz p)) (fun p => ev cz (ev cc p)) = true := by
  decide +kernel

@[expose] def ctOK : Bool :=
  (List.range 6).all fun j => (List.range 3).all fun p => (List.range 3).any fun q =>
    eqOn (fun r => ev cc (ev (ct (3 * j + p)) r))
      (fun r => ev (ct (3 * ((j + 1) % 3 + 3 * (j / 3)) + q)) (ev cc r))

theorem ct_ok : ctOK = true := by decide +kernel

theorem cx_neg : (!eqOn (fun p => ev cc (ev cx p)) (fun p => ev cx (ev cc p))) = true := by
  decide +kernel

theorem ct_neg : (!(List.range 3).any fun q =>
    eqOn (fun r => ev cc (ev (ct 0) r)) (fun r => ev (ct q) (ev cc r))) = true := by
  decide +kernel


@[expose] noncomputable def cE : GJ := eltOf cArr okc

theorem repF_c : RepF (ev cc) cE := repF_of_rep (rep_eltOf okc) okL_c

theorem c_fact : ∃ c : GJ, c * xJ * c⁻¹ = xJ * zJ ∧ c * zJ * c⁻¹ = zJ ∧
    ∀ j < 6, ∀ p < 3, ∃ q < 3,
      c * tJ (3 * j + p) * c⁻¹ = tJ (3 * ((j + 1) % 3 + 3 * (j / 3)) + q) := by
  refine ⟨cE, ?_, ?_, fun j hj p hp => ?_⟩
  · have e : cE * xJ = xJ * zJ * cE :=
      eq_of_repF (repF_mul repF_c repF_x) (repF_mul (repF_mul repF_x repF_z) repF_c)
        fun _ hr => eqOn_spec cx_ok hr
    rw [e, mul_inv_cancel_right]
  · have e : cE * zJ = zJ * cE :=
      eq_of_repF (repF_mul repF_c repF_z) (repF_mul repF_z repF_c) fun _ hr => eqOn_spec cz_ok hr
    rw [e, mul_inv_cancel_right]
  · have h := List.all_eq_true.1 ct_ok j (List.mem_range.2 hj)
    obtain ⟨q, hq, h2⟩ := List.any_eq_true.1 (List.all_eq_true.1 h p (List.mem_range.2 hp))
    have hq3 := List.mem_range.1 hq
    refine ⟨q, hq3, ?_⟩
    have e : cE * tJ (3 * j + p) = tJ (3 * ((j + 1) % 3 + 3 * (j / 3)) + q) * cE :=
      eq_of_repF (repF_mul repF_c (repF_tJ (by omega))) (repF_mul (repF_tJ (by omega)) repF_c)
        fun _ hr => eqOn_spec h2 hr
    rw [e, mul_inv_cancel_right]

end CFSG.KD.R148Dc.J2C

end
