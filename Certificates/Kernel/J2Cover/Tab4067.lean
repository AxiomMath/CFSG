module

public import Certificates.Kernel.J2Cover.Orb
public import CFSG.Certificates.Kernel.LBindSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.J2.Simple
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover.Tab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.ComponentClassification.J2Cover.Models
open CFSG.QuasithinUnique.Setup.X1

theorem tA : lbindK (j2ta_0.toList ++ j2ta_1.toList) 315 9 (PA.S 0) = true := by quickRfl
theorem tB : lbindK (j2tb_0.toList ++ j2tb_1.toList) 315 9 (PA.S 1) = true := by quickRfl

theorem tabOfFn (t : Array UInt32) :
    (Array.ofFn (n := 315) fun i => CFSG.Sporadic.Th.Native.ap t i.val).toList =
      (List.range 315).map (CFSG.Sporadic.Th.Native.ap t) := by
  rw [Array.toList_ofFn]
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i _ _ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]

theorem facts : j2Data.ta.toList = CFSG.QuasithinUnique.K1.SporadicPerm.j2ta ∧
    j2Data.tb.toList = CFSG.QuasithinUnique.K1.SporadicPerm.j2tb := by
  have ea : j2Data.ta.toList = j2ta_0.toList ++ j2ta_1.toList := by
    simp [j2Data, CFSG.QuasithinUnique.Setup.X1.j2ta]
  have eb : j2Data.tb.toList = j2tb_0.toList ++ j2tb_1.toList := by
    simp [j2Data, CFSG.QuasithinUnique.Setup.X1.j2tb]
  have ha := congrArg Array.toList (lbindK_sound tA)
  have hb := congrArg Array.toList (lbindK_sound tB)
  rw [List.toList_toArray] at ha hb
  rw [ea, eb, ha, hb, ← alphaArr_eq, ← betaArr_eq]
  unfold alphaArr betaArr CFSG.QuasithinUnique.K1.SporadicPerm.j2ta
    CFSG.QuasithinUnique.K1.SporadicPerm.j2tb
  exact ⟨tabOfFn _, tabOfFn _⟩

end CertificateChecks.KernelJ2Cover.Tab

end
