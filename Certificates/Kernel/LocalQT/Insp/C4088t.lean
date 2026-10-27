module

public import Certificates.Data.Kernel.LocalQT.Insp
public import Certificates.Data.Kernel.LocalQT.SylE
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4088

open CFSG.KC.LQT.Insp CFSG.KC.LQT.Syl CFSG.KC.LQT.W CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.QuasithinUnique.Vol2Native.L239.M23Insp CFSG.Blueprint

theorem hGg : gens.map (fun x : ↥NativeSporadic.M23 => codeP (x : Equiv.Perm (Fin 23))) =
    [29396287020561317414859794500619265, 4436007312844787929641103698034959] := by
  decide +kernel

theorem kR : reachTK 23 5 (List.map (evalZK 23 [29396287020561317414859794500619265,
    4436007312844787929641103698034959]) ksWords) tupleCodes tupleParent tupleLabel 5516578 =
      true := by quickRfl

theorem kN : codesTK 23 5 tupleCodes = true := by quickRfl

end CFSG.KD.LQT.C4088

end
