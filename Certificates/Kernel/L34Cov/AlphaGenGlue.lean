
module

public import Certificates.Kernel.L34Cov.AlphaGenChecks
public import Certificates.Kernel.L34Cov.AlphaGlue
public import Certificates.Kernel.L34Cov.T1Glue
public import CFSG.Certificates.Kernel.L34Cov.AlphaGenSound

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CertificateChecks.KernelL34W

#kc_forall_tree ch22219ag_all (fun i => alGensOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW
  TwC.codes AlX.F (UAC.codes.getD i []) (UBC.codes.getD i []) i = true) 36
  CertificateChecks.KernelL34Cov.ch22219ag.a

theorem zeta_eq (uA uB : List (Fin 2 × Bool)) (j : ℕ) (hj : j < 2)
    {v : ℕ} (h : zvOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab
      (invW (([uA, uB].getD j []).map letterCode) ++
        substC [uA.map letterCode, uB.map letterCode] (FW.getD j [])) v = true) :
    (cv ([uA, uB].getD j []))⁻¹ * cv ((autWs uA uB).getD j []) = zc v := by
  have hU : [uA.map letterCode, uB.map letterCode] = [uA, uB].map (List.map letterCode) := rfl
  have e : invW (([uA, uB].getD j []).map letterCode) ++
      substC [uA.map letterCode, uB.map letterCode] (FW.getD j []) =
      (FreeGroup.invRev ([uA, uB].getD j []) ++ (autWs uA uB).getD j []).map letterCode := by
    rw [List.map_append, map_letterCode_invRev, FW_getD, hU, ← map_letterCode_substWord]
    interval_cases j <;> rfl
  rw [e] at h
  have := cv_of_zvOK vt_k modelA modelB h
  rwa [cv_append, cv_invRev] at this

theorem alpha_gen_spec {i g : ℕ} (hi : i < 36)
    (hg : g ∈ [1, 2, 16, 20]) :
    cv (substWord (aut i) (tw g)) = cv (tw (alphaEntry i g).1) * cv (zOf (alphaEntry i g)) := by
  obtain ⟨α, hα, hα'⟩ := exists_alphaLift hi
  have h := ch22219ag_all i hi
  have hcA : (uA i).map letterCode = UAC.codes.getD i [] := by
    rw [(uA_eq i).1]
    exact map_letterCode_decL (uA_eq i).2
  have hcB : (uB i).map letterCode = UBC.codes.getD i [] := by
    rw [(uB_eq i).1]
    exact map_letterCode_decL (uB_eq i).2
  rw [← hcA, ← hcB] at h
  unfold alGensOK at h
  rw [bindB_eq, bindB_eq] at h
  generalize zvC VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab (invW ((uA i).map letterCode) ++
    substC [(uA i).map letterCode, (uB i).map letterCode] (FW.getD 0 [])) = vA at h
  generalize zvC VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab (invW ((uB i).map letterCode) ++
    substC [(uA i).map letterCode, (uB i).map letterCode] (FW.getD 1 [])) = vB at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hzA, hzB, h1, h2, h16, h20⟩ := h
  have zA := zeta_eq (uA i) (uB i) 0 (by norm_num) hzA
  have zB := zeta_eq (uA i) (uB i) 1 (by norm_num) hzB
  have hg' : alGenOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab TwC.codes AlX.F
      ((uA i).map letterCode) ((uB i).map letterCode) vA vB i g = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h16
    · exact h20
  rw [← hα, hα']
  change cv (substWord [uA i, uB i] (tw g)) *
    ((cv ([uA i, uB i].getD 0 []))⁻¹ * cv ((autWs (uA i) (uB i)).getD 0 [])) ^ expOf 0 (tw g) *
    ((cv ([uA i, uB i].getD 1 []))⁻¹ * cv ((autWs (uA i) (uB i)).getD 1 [])) ^ expOf 1 (tw g) = _
  rw [zA, zB]
  exact alGen_sound vt_k modelA modelB alOf tw_codes hi (gens_lt g hg) hg'

end CertificateChecks.KernelL34Cov

end
