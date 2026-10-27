module

public import Certificates.Data.Kernel.Ivk8NormP
public import Certificates.Data.Kernel.SporSch.J1Cent
public import Certificates.Kernel.SporSch.J1.Levels
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CFSG.KS.Ivk8NormP.J1

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.KC.Enum CFSG.KS
  CFSG.KS.SporSch.J1C CertificateChecks.KernelSporSch

@[expose] def invW (w : List Int) : List Int := w.reverse.map Neg.neg

@[expose] noncomputable def evA (w : List Int) : Nat :=
  wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1L.S J1L.SI) w

@[expose] def j1Gw : List (List Int) :=
  [[1],
  [2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2,
    1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2],
  [2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1,
    2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
  [2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2,
    2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2]]

@[expose] noncomputable def gG (k : Nat) : Nat := evA (j1Gw.getD (k - 1) [])

@[expose] noncomputable def gGI (k : Nat) : Nat := evA (invW (j1Gw.getD k []))

@[expose] noncomputable def evG (w : List Int) : Nat :=
  wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK (fun k => gG (k + 1)) gGI) w

@[expose] noncomputable def zN : Nat := evA [1]

@[expose] def j1O : Nat :=
  2302229249317036839770445359919805368331291665537390531686505101319733901270334629269805479325983339954355046979651311014008267251874709182144522

@[expose] def j1Xw : List (List Int) := [[-1], [-4, -4, -2, -1, -3, -2], [-3, -4, -2]]

@[expose] def j1C1w : List Int :=
  [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2]

@[expose] def j1C2w : List Int :=
  [2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2]

@[expose] noncomputable def frN (cw : List Int) (x : Nat) : Nat :=
  pcomp 3080 12 (mask 12) (evA (invW cw)) (pcomp 3080 12 (mask 12) x (evA cw))

@[expose] noncomputable def j1Sig : List (VP 40) :=
  [mkV 40 (1066114297847938375783413301453253569629014309383940159390381488340480001,
    1066114297847938375783413301453253569629014309383940159390381488340480001) (by decide +kernel),
  mkV 40 (502331249664226051088163480093050415744026940535100299764851399964254862,
    310303775787789100835514965419422013326090053836636445450777508498929700) (by decide +kernel),
  mkV 40 (310296988878130189036067898799382309727925106361830226551322577998762048,
    478427788338474182442597545319415158952263522447838538696690628322488384) (by decide +kernel),
  mkV 40 (169211076173953120020114634617610872911115641207259126540555182751471390,
    646325289306564819132413568298439653933529910653661305366636604754285653) (by decide +kernel)]

@[expose] noncomputable def j1Fr1 : List (VP 40) :=
  [mkV 40 (646251109597151085597046011162524131321698003182116880358620885713199496,
    646251109597151085597046011162524131321698003182116880358620885713199496) (by decide +kernel),
  mkV 40 (1066114297847938375783413301453253569629014309383940159390381488340480001,
    1066114297847938375783413301453253569629014309383940159390381488340480001) (by decide +kernel),
  mkV 40 (1007753480473847482758913159310265201555640646723554633946932032987526872,
    1007753480473847482758913159310265201555640646723554633946932032987526872) (by decide +kernel)]

@[expose] noncomputable def j1Fr2 : List (VP 40) :=
  [mkV 40 (559219691013643889217867930395667406536966118068545983018285207580873490,
    559219691013643889217867930395667406536966118068545983018285207580873490) (by decide +kernel),
  mkV 40 (450497179957055334440423771481487182301281668615202325431487193386611852,
    450497179957055334440423771481487182301281668615202325431487193386611852) (by decide +kernel),
  mkV 40 (786167686300401067065050270723738417682916477920939377853278704044631449,
    786167686300401067065050270723738417682916477920939377853278704044631449) (by decide +kernel)]

@[expose] noncomputable def j1Strong : List (VP 40) := buildV j1Sig []

@[expose] noncomputable def j1Xs : List (VP 40) := j1Xw.map (evV j1Sig)

@[expose] noncomputable def j1Enum : List Nat := (enumV j1Strong #v[0, 2]).map fun y => y.1.1

@[expose] noncomputable def wits (S : List (VP 40)) : List (Nat × Nat) :=
  (subprodsV S).tail.map Subtype.val

@[expose] noncomputable def j1W (L : List Nat) : Bool :=
  chkP 40 6 3 (wits j1Xs) L && chkP 40 6 5 (wits j1Xs) L && chkP 40 6 3 (wits j1Fr1) L &&
    chkP 40 6 5 (wits j1Fr1) L && chkP 40 6 3 (wits j1Fr2) L && chkP 40 6 5 (wits j1Fr2) L

theorem ch5253_j1_sorted : sortedOK 12 j1O 40 3080 = true := by quickRfl

theorem ch5253_j1_res : (List.range 4).all (fun k =>
    Nat.beq (pcomp 3080 12 (mask 12) (gG (k + 1)) zN) (pcomp 3080 12 (mask 12) zN (gG (k + 1))) &&
      resOK 12 j1O 40 (gG (k + 1)) (j1Sig.getD k (oneV 40))) = true := by quickRfl

theorem ch5253_j1_conj :
    (Nat.beq (pcomp 3080 12 (mask 12) (evA j1C1w) zN)
        (pcomp 3080 12 (mask 12) (evG (j1Xw.getD 1 [])) (evA j1C1w)) &&
      Nat.beq (pcomp 3080 12 (mask 12) (evA j1C2w) zN)
        (pcomp 3080 12 (mask 12) (pcomp 3080 12 (mask 12) zN (evG (j1Xw.getD 1 [])))
          (evA j1C2w)) &&
      (List.range 3).all (fun j =>
        resOK 12 j1O 40 (frN j1C1w (evG (j1Xw.getD j []))) (j1Fr1.getD j (oneV 40)) &&
          resOK 12 j1O 40 (frN j1C2w (evG (j1Xw.getD j []))) (j1Fr2.getD j (oneV 40)))) =
      true := by
  quickRfl

theorem ch5253_j1_sch : schV j1Strong #v[0, 2] = true := by quickRfl

theorem ch5253_j1_ord : Nat.beq (ordV j1Strong #v[0, 2]) 120 = true := by quickRfl

theorem ch5253_j1_xs : (j1Xs.all invoV && j1Xs.all fun x => j1Xs.all (commV x)) = true := by
  quickRfl

theorem ch5253_j1_w : j1W j1Enum = true := by quickRfl

end CFSG.KS.Ivk8NormP.J1

end
