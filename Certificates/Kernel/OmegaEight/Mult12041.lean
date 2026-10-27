module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverData
public import CFSG.Certificates.Kernel.CycTabSound
import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.OmegaEight.Mult12041Gen
import Mathlib.Tactic.FinCases
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

#kc_eval CertificateChecks.KernelO8.Mult12041 D CertificateChecks.KernelO8.Mult12041.relStep

namespace CertificateChecks.KernelO8.Mult12041

open CFSG.KC.CycTab CFSG.EvenSmallLie.OmegaEight.Cover CFSG.Sporadic.Schreier

@[expose] def cs : List (List (List Nat)) := [rhoCycles 0, rhoCycles 1, rhoCycles 2, rhoCycles 3]

theorem gens_true : gensOK 240 cs D.TT = true := by quickRfl

theorem rels_true : relsOK 240 D.TT D.RS = true := by quickRfl

theorem rs_eq : rels.map (List.map codeOf) = D.RS := by decide +kernel

theorem letters : LetterOK D.TT rhoGens := by
  refine gens_sound (by decide) (fun i => ?_) gens_true
  rw [rhoGens, cycPerm, tab_eq]
  fin_cases i <;> rfl

theorem relator_sq : (rels.all fun r => decide (rhoWord r * rhoWord r = 1)) = true := by
  rw [List.all_eq_true]
  intro r hr
  rw [decide_eq_true_eq]
  exact sq_sound letters rels_true r (rs_eq ▸ List.mem_map_of_mem hr)

end CertificateChecks.KernelO8.Mult12041

end
