module

public import Certificates.Kernel.SporSch.HN.Pt2109
public import Certificates.Kernel.SporSch.HN.C13608K
public import Certificates.Kernel.SporSch.HN.C13608GK
public import Certificates.Kernel.HNChain.FormFacts
public import CFSG.Certificates.Kernel.SporSch.HNXDotSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HN13608

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HNArrS CertificateChecks.KernelSporSch.HNPt2103
open CertificateChecks.KernelSporSch.HNPt2109 CFSG.KD.HN13608 CFSG.KD.LgHNX Matrix

local notation "OM" => ordMat 5 133 13 1729
local notation "R" => CFSG.KD.HNPt.R
local notation "mm" => CFSG.KC.LL.HN.mm
local notation "g19" => aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ
local notation "u19" => aJ * (g19⁻¹ * bJ * g19)

theorem codes_ok : ec = ([2, 4, 5, 8, 5, 4, 2] : List ℤ).map scode := by
  decide +kernel

theorem canon_of_lt {cs : List ℕ} (h : ∀ c ∈ cs, c < 36) : ∀ c ∈ cs, Canon 5 133 13 (R c) :=
  fun _ hc => R_canon (h _ hc)

theorem mA_eq : OM (R 34) = matJ aJ := by
  rw [R_mat (c := 34) (by norm_num), genJ, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem mB_eq : OM (R 35) = matJ bJ := by
  rw [R_mat (c := 35) (by norm_num), genJ, if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num)]

theorem stepA {X : ℕ} {x : JH} (h : Canon 5 133 13 X ∧ OM X = matJ x) :
    Canon 5 133 13 (mm X (R 34)) ∧ OM (mm X (R 34)) = matJ (x * aJ) := by
  have cA := R_canon (c := 34) (by norm_num)
  refine ⟨(HNXP.mm_sound h.1 cA).1, ?_⟩
  rw [(HNXP.mm_sound h.1 cA).2, h.2, mA_eq, HNArr.matJ_mul]

theorem stepB {X : ℕ} {x : JH} (h : Canon 5 133 13 X ∧ OM X = matJ x) :
    Canon 5 133 13 (mm X (R 35)) ∧ OM (mm X (R 35)) = matJ (x * bJ) := by
  have cB := R_canon (c := 35) (by norm_num)
  refine ⟨(HNXP.mm_sound h.1 cB).1, ?_⟩
  rw [(HNXP.mm_sound h.1 cB).2, h.2, mB_eq, HNArr.matJ_mul]

theorem g_mat : Canon 5 133 13 gL13608 ∧ OM gL13608 = matJ g19 :=
  stepA (stepB (stepA (stepB (stepA (stepB (stepA (stepB (stepA (stepB (stepB
    ⟨R_canon (c := 34) (by norm_num), mA_eq⟩))))))))))

theorem gi_mat :
    Canon 5 133 13 (wordC R gic13608) ∧ OM (wordC R gic13608) = matJ g19⁻¹ := by
  have hgi := HNXP.wordC_sound gic13608 (canon_of_lt (by decide))
  have e := congrArg OM inv_ok
  rw [(HNXP.mm_sound g_mat.1 hgi.1).2, HNXP.one_ord, g_mat.2] at e
  exact ⟨hgi.1, HNArr.mat_inv_of_mul e⟩

theorem U_mat : Canon 5 133 13 U ∧ OM U = matJ u19 := by
  have cA := R_canon (c := 34) (by norm_num)
  have cB := R_canon (c := 35) (by norm_num)
  have h1 := HNXP.mm_sound gi_mat.1 cB
  have h2 := HNXP.mm_sound h1.1 g_mat.1
  have h3 := HNXP.mm_sound cA h2.1
  rw [u_shape]
  refine ⟨h3.1, ?_⟩
  rw [h3.2, h2.2, h1.2, gi_mat.2, g_mat.2, mA_eq, mB_eq, ← HNArr.matJ_mul, ← HNArr.matJ_mul,
    ← HNArr.matJ_mul]

theorem FM_mat : Canon 5 133 13 FM ∧ OM FM = formM := by
  have hM : toMat 5 133 rowsM = formM := by
    rw [rowsM, toMat_rowsOf, formM_eq]
  refine ⟨HNXP.canon_of_validHN form_ok.1, (om_rows form_ok.2).trans ?_⟩
  rw [← CertificateChecks.KernelHNChain.Form.rowsM_eq, hM]

theorem GQ_mat :
    Canon 5 133 13 GQ ∧ OM GQ = formM * (matJ u19 + matJ u19 ^ 2) := by
  have hU := U_mat
  have h2 := HNXP.mm_sound hU.1 hU.1
  have h3 := HNXP.addHN_sound hU.1 h2.1
  have h4 := HNXP.mm_sound FM_mat.1 h3.1
  rw [gq_ok]
  refine ⟨h4.1, ?_⟩
  rw [h4.2, h3.2, h2.2, FM_mat.2, hU.2, sq]

theorem E_mat :
    Canon 5 133 13 E ∧ OM E = matJ (wJ sL [2, 4, 5, 8, 5, 4, 2]) :=
  strong_elem words_ok.2.1 codes_ok (by decide)

theorem card_dot_of {N : ℕ}
    (htot : ∑ b ∈ Finset.range 17813, dotLeaf TX CM3 M MR L1 ONES GQ 1 b (hnxC b) = N) :
    ((Finset.range nPts).filter fun i =>
      PK i ⬝ᵥ ((formM * (matJ u19 + matJ u19 ^ 2)) *ᵥ PK i) = 1).card = N := by
  have h := HNXP.card_dot_eq (T := TX) consts_parts.1 consts_parts.2 consts GQ_mat.1 (v := 1)
    (by norm_num)
  rw [htot] at h
  rw [← h]
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  rw [PK_eq (Finset.mem_range.1 hi), GQ_mat.2, Nat.cast_one]

theorem card_fix_e_of {N : ℕ}
    (htot : ∑ b ∈ Finset.range 17813, fixLeaf TX 464 CM3 M [GE] b (hnxC b) = N) :
    ((Finset.range nPts).filter fun i => gi (wJ sL [2, 4, 5, 8, 5, 4, 2]) i = i).card = N :=
  card_fix_of E_mat.1 E_mat.2 words_ok.2.2 htot

end CertificateChecks.KernelSporSch.HN13608

end
