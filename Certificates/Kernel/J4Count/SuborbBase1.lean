
module

public import Certificates.Kernel.J4Count.SuborbBase

public import Certificates.Kernel.J4Count.FixZBase1
public import Certificates.Kernel.J4Count.ChecksQ1
public import Certificates.Kernel.J4Hub.Struct
public import Certificates.Kernel.J4Q.Mat
public import CFSG.Sporadic.J4.QT2LocX0CentMainBase1
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.H13.J4CentralizerBase1
public import Certificates.Kernel.J4Count.HOrderBase1
public import Certificates.Kernel.SporSch.J4S.NoCP

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.J4.Struct CertificateChecks.KernelSporSch

section Dvd

variable {G X : Type*} [Group G] [Finite G] [MulAction G X]

end Dvd

theorem qv_eq {l : ℕ} (hl : l < 7) : qv l = (mRep l)⁻¹ • v := (mRep_inv_smul_v hl).symm

theorem qv_zero : qv 0 = v := by
  rw [qv_eq (by norm_num), mRep_zero, inv_one, one_smul]

theorem qv_mem {l : ℕ} (hl : l < 7) : qv l ∈ orbit J v := ⟨(mRep l)⁻¹, (qv_eq hl).symm⟩

instance normal_NH : (N.subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer N_le_H).2 H_le_normalizer

theorem card_NH : Nat.card (N.subgroupOf H) = 2048 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le_H).toEquiv, card_N]
  norm_num

theorem fixCard_q1 : fixCard CFSG.Sporadic.J4.QT2.q1Row = 2 := by
  have hq : CFSG.Sporadic.J4.QT2.q1Row = toRow (toVecD 112 Q1N) := by
    rw [CFSG.Sporadic.J4.QT2.q1Row, q1_toVec]
  rw [hq, fixCard_eq_card _
    (fun a => Nat.beq (Nat.mod (etaV unMats Q1N a) (Nat.pow 2 112)) Q1N = true) ?_]
  · have h := Nat.eq_of_beq_eq_true fix_q1
    unfold cntQ1 at h
    rw [J4NoCP.cntK_eq] at h
    refine Eq.trans (congrArg Finset.card (Finset.filter_congr fun a _ => ?_)) h
    rw [J4NoCP.etaV_eq]
  · intro a _
    rw [η_smul_toRow, ← ofRow_inj, Nat.beq_eq]
    change toVecD 112 _ = toVecD 112 _ ↔ etaV unMats Q1N a % 2 ^ 112 = Q1N
    rw [toVecD_eq_iff, Nat.mod_eq_of_lt (b := 2 ^ 112) (by norm_num [Q1N] : Q1N < 2 ^ 112)]

theorem q1_mem :
    CFSG.Sporadic.J4.QT2.q1Row ∈ orbit J v := by
  obtain ⟨g, -, hg⟩ := CFSG.Sporadic.J4.QT2.exists_of_mem_pts CertificateChecks.KernelJ4Q.matFacts
    CFSG.Sporadic.J4.QT2.q1_mem_pts
  refine ⟨g, ?_⟩
  change g • v = _
  rw [v_eq_root]
  exact hg

end CertificateChecks.KernelJ4Count

end
