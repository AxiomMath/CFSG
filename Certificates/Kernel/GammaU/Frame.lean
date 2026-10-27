
module

public import Certificates.Kernel.GammaU.FrameOK
public import Certificates.Kernel.GammaU.Triple
public import Certificates.Kernel.GammaU.CensusCfgOK
public import CFSG.Certificates.Kernel.GammaUFrameSound

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUF

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem compGens_mem {c l : Nat} (hc : c < 32) (hl : l < 5) :
    ∃ U ∈ gammaU, ∀ y, U y = linOfRows ((ResPair.compGens c).getD l #[]) y := by
  obtain ⟨U, hU⟩ := CFSG.KD.GUCB.exists_isP_cg c hc _ (mem_five.2 ⟨l, hl, rfl⟩)
  have h := cf16966_cg
  unfold cgOK at h
  have hk := (allBelow_iff _ _).1 h (5 * c + l) (by omega)
  exact ⟨U, guOK_spec CFSG.KD.GUTB.linP_TH hk hU, fun y => by
    rw [hU, CFSG.KD.GUCB.linP_cg hc hl]⟩

theorem dt_mem {j : Nat} (hj : j < 108) {T : GL} (hT : IsP T (look CFSG.KD.GUCC.DT j)) :
    T ∈ gammaU ∧ T (vecOf a0) = vecOf a0 := by
  have h := cf16966_dt
  unfold dtsOK at h
  exact dtOK_spec CFSG.KD.GUTB.linP_TH ((allBelow_iff _ _).1 h j hj) hT

theorem te_mem {n : Nat} (hn : n < CFSG.KD.GUCC.NE) {T : GL}
    (hT : IsP T (look CFSG.KD.GUCC.TE n)) : T ∈ gammaU := by
  have h := cf16966_te
  unfold teOK at h
  exact guOK_spec CFSG.KD.GUTB.linP_TH ((allBelow_iff _ _).1 h n hn) hT

theorem sa_lists : SA.length = 2 ∧ ∀ s < 2, mulP (nthD 0 SA s) (nthD 0 SAI s) = idP := by
  have h := cf16966_sa
  unfold saOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, allBelow_iff] at h
  exact ⟨h.1.1, h.2⟩

theorem sa_perm {s j : Nat} (hs : s < 2) (hj : j < 108) :
    ∃ j' < 108, ∀ U T T' : GL, (∀ y, U y = linOfRows (saGens.getD s #[]) y) →
      IsP T (look CFSG.KD.GUCC.DT j) → IsP T' (look CFSG.KD.GUCC.DT j') →
      (spanOf d0).map ((U * T : GL) : V12 →ₗ[ZMod 2] V12) =
        (spanOf d0).map (T' : V12 →ₗ[ZMod 2] V12) := by
  have hsj : sjOK s = true := by
    interval_cases s
    exacts [cf16966sj0, cf16966sj1]
  unfold sjOK at hsj
  have hr := (allBelow_iff _ _).1 hsj j hj
  rw [Bool.and_eq_true, Nat.blt_eq] at hr
  obtain ⟨hlt, hat⟩ := hr
  obtain ⟨hSA, hrows⟩ := cf16966_sap
  have hlen : s < saGens.length := by
    rw [show saGens.length = 2 from rfl]
    exact hs
  refine ⟨_, hlt, fun U T T' hU hT hT' => ?_⟩
  have hUP : IsP U (nthD 0 SA s) := by
    rw [hSA, nthD_map _ _ _ #[] hlen]
    have hmem : saGens.getD s #[] ∈ saGens := by
      rw [getD_of_lt _ hlen]
      exact List.getElem_mem hlen
    exact (isP_packR (List.all_eq_true.1 hrows _ hmem) U).2 hU
  have hd : D0F = d0 := rfl
  rw [← hd]
  exact sjAt_spec hat hUP (hUP.inv (sa_lists.2 s hs)) hT hT'

end CFSG.KD.GUF

end
