
module

public import Certificates.Kernel.L34Cov.AlphaChecks
public import Certificates.Kernel.L34Cov.WordsGlue
public import Certificates.Kernel.L34Cov.Glue
public import CFSG.Certificates.Kernel.L34Cov.AlphaOKSound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

#kc_forall_tree ch22219al_all (fun i => alphaOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW
  (UAC.codes.getD i []) (UBC.codes.getD i []) = true) 36 CertificateChecks.KernelL34Cov.ch22219al.a

theorem exists_alphaLift {i : ℕ} (hi : i < 36) :
    ∃ α : Cover →* Cover, (∀ w, α (cv w) = cv (substWord (aut i) w)) ∧
      ∀ w, α (cv w) = cv (substWord [uA i, uB i] w) *
        ((cv (uA i))⁻¹ * cv ((aut i).getD 0 [])) ^ expOf 0 w *
        ((cv (uB i))⁻¹ * cv ((aut i).getD 1 [])) ^ expOf 1 w := by
  have h := ch22219al_all i hi
  have hcA : (uA i).map letterCode = UAC.codes.getD i [] := by
    rw [(uA_eq i).1]
    exact map_letterCode_decL (uA_eq i).2
  have hcB : (uB i).map letterCode = UBC.codes.getD i [] := by
    rw [(uB_eq i).1]
    exact map_letterCode_decL (uB_eq i).2
  rw [← hcA, ← hcB] at h
  exact alphaHom_of_alphaOK vt_k modelA modelB h

end CertificateChecks.KernelL34Cov

end
