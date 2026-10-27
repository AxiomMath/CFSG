module

public import CFSG.Certificates.Kernel.TwD5ReflKGlue
public import Certificates.Kernel.TwD5ReflK.ChecksAll
public import Certificates.Kernel.TwD5ReflK.ChecksAllK1

public section

namespace CFSG.KD.TwD5RAll

open CFSG.KC.TwD5R CFSG.StandardType.FrameRoute.FS81

theorem goodsAll_dec : ∀ c : Fin 4, reflK (getN goodsAll c) = goodAll c := by decide +kernel

theorem k1All : K1Prop false repTab nrep := by
  refine k1Prop_of (fun i => [K0, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14,
    K15, K16, K17, K18, K19, K20, K21, K22, K23, K24, K25, K26].getD i []) ?_
  intro i hi
  interval_cases i
  · exact ch709602k1_0
  · exact ch709602k1_1
  · exact ch709602k1_2
  · exact ch709602k1_3
  · exact ch709602k1_4
  · exact ch709602k1_5
  · exact ch709602k1_6
  · exact ch709602k1_7
  · exact ch709602k1_8
  · exact ch709602k1_9
  · exact ch709602k1_10
  · exact ch709602k1_11
  · exact ch709602k1_12
  · exact ch709602k1_13
  · exact ch709602k1_14
  · exact ch709602k1_15
  · exact ch709602k1_16
  · exact ch709602k1_17
  · exact ch709602k1_18
  · exact ch709602k1_19
  · exact ch709602k1_20
  · exact ch709602k1_21
  · exact ch709602k1_22
  · exact ch709602k1_23
  · exact ch709602k1_24
  · exact ch709602k1_25
  · exact ch709602k1_26

theorem t5ReflAll_of_checks : T5ReflAll :=
  refl_of_checks (fx := false) (LG := ![LG0, LG1, LG2, LG3]) (OW := ![OW0, OW1, OW2, OW3]) rfl
    goodsAll_dec ch709602gens k1All ch709602tab ch709602reps ch709602repN ch709602bad
    ch709602k12 ch709602lh
    (fun c => by
      fin_cases c
      · exact ch709602lg0
      · exact ch709602lg1
      · exact ch709602lg2
      · exact ch709602lg3)
    (fun c => by
      fin_cases c
      · exact ch709602k3a
      · exact ch709602k3b
      · exact ch709602k3c
      · exact ch709602k3d)

end CFSG.KD.TwD5RAll

end
