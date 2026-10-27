module

public import CFSG.Certificates.Kernel.TwD5ReflKGlue
public import Certificates.Kernel.TwD5ReflK.ChecksFix
public import Certificates.Kernel.TwD5ReflK.ChecksFixK1

public section

namespace CFSG.KD.TwD5RFix

open CFSG.KC.TwD5R CFSG.StandardType.FrameRoute.FS81

theorem goodsFix_dec : ∀ c : Fin 3, reflK (getN goodsFix c) = goodFix c := by decide +kernel

theorem k1Fix : K1Prop true repTab nrep := by
  refine k1Prop_of (fun i => [K0, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14,
    K15, K16, K17, K18, K19, K20, K21, K22, K23, K24, K25, K26].getD i []) ?_
  intro i hi
  interval_cases i
  · exact ch709601k1_0
  · exact ch709601k1_1
  · exact ch709601k1_2
  · exact ch709601k1_3
  · exact ch709601k1_4
  · exact ch709601k1_5
  · exact ch709601k1_6
  · exact ch709601k1_7
  · exact ch709601k1_8
  · exact ch709601k1_9
  · exact ch709601k1_10
  · exact ch709601k1_11
  · exact ch709601k1_12
  · exact ch709601k1_13
  · exact ch709601k1_14
  · exact ch709601k1_15
  · exact ch709601k1_16
  · exact ch709601k1_17
  · exact ch709601k1_18
  · exact ch709601k1_19
  · exact ch709601k1_20
  · exact ch709601k1_21
  · exact ch709601k1_22
  · exact ch709601k1_23
  · exact ch709601k1_24
  · exact ch709601k1_25
  · exact ch709601k1_26

theorem t5ReflFix_of_checks : T5ReflFix :=
  refl_of_checks (fx := true) (LG := ![LG0, LG1, LG2]) (OW := ![OW0, OW1, OW2]) rfl
    goodsFix_dec ch709601gens k1Fix ch709601tab ch709601reps ch709601repN ch709601bad
    ch709601k12 ch709601lh
    (fun c => by
      fin_cases c
      · exact ch709601lg0
      · exact ch709601lg1
      · exact ch709601lg2)
    (fun c => by
      fin_cases c
      · exact ch709601k3a
      · exact ch709601k3b
      · exact ch709601k3c)

end CFSG.KD.TwD5RFix

end
