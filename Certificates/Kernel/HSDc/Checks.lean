module

public import Certificates.Data.Kernel.HSDc.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs
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
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.HSDc

open CFSG.KC.SLDc CFSG.QuasithinUnique.K1.SporadicPerm

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

theorem mems : (List.range 5).all memOK = true := by
  quickRfl

theorem invs : invOK = true := by
  quickRfl

theorem mws : mwOK = true := by
  quickRfl

theorem sepB : (J.sep == hsB) = true := by
  quickRfl

theorem mwLenB : (J.mw.length == 5) = true := by
  quickRfl

theorem mw0B : (J.mw.getD 0 [] == []) = true := by
  quickRfl

end CFSG.KD.HSDc

end
