module

public import Certificates.Kernel.He589208.D
public import Certificates.Kernel.He589208.T
public import Certificates.Data.Kernel.DcK

public section

namespace CFSG.KD.He589208

open CFSG.KC.DcK CFSG.KC.E64F CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.HeC0
open CFSG.QuasithinUnique.K1.SporadicPerm (slpTabsA)
@[expose] noncomputable def im (c p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 c p

@[expose] def exOf (ab : Nat → Nat → Nat) (ws : List (List Nat)) (i : Nat) : Nat → Nat :=
  wordF ab (ws.getD i [])

@[expose] noncomputable def abc (l : Nat) : Nat := [S.TF 0, S.TF 1, P.TF 0, P.TF 1].getD l 0

@[expose] noncomputable def ab (l p : Nat) : Nat := im (abc l) p

@[expose] noncomputable def rtc (t : Nat) : Nat := [S.TF 7, S.TF 15, S.TF 25].getD t 0

@[expose] noncomputable def rt (t p : Nat) : Nat := im (rtc t) p

@[expose] noncomputable def rti (t p : Nat) : Nat := im (P.TF (t + 2)) p

@[expose] noncomputable def lbF (q : Nat) : Nat := im (P.TF 5) q

@[expose] noncomputable def QF (i : Nat) : Nat := im (P.TF 6) i

@[expose] noncomputable def vtF (q : Nat) : Nat := im (P.TF 7) q

@[expose] noncomputable def ER : EnumK := recK 512 5 RR.TF

@[expose] noncomputable def EV0 : EnumK := recK 7680 5 V0.TF

@[expose] noncomputable def EV1 : EnumK := recK 7680 5 V1.TF

@[expose] def w0 : List (List Nat) := (vData.headD ([], 0)).1

@[expose] def w1 : List (List Nat) := ((vData.drop 1).headD ([], 0)).1

@[expose] noncomputable def K : DcK where
  n := 8330
  B := B
  ab := ab
  nr := 3
  rt := rt
  rti := rti
  R := ER
  lb := lbF
  reps := (wordsK T.reps.chars).toArray
  edges := ((edgesK T.edges.chars).getD []).toArray
  c0 := root
  inEdge := ((natsK T.inEdge.chars).getD []).toArray
  dIn := ((natsK T.dIn.chars).getD []).toArray
  reach := (natsK T.reach.chars).getD []
  outEdge := ((natsK T.outEdge.chars).getD []).toArray
  dOut := ((natsK T.dOut.chars).getD []).toArray
  Vs := [(w0, exOf ab w0, EV0), (w1, exOf ab w1, EV1)]
  order := 161280
  hpos j k := im (H.TF k) j

@[expose] noncomputable def IV : List Nat :=
  (List.range 6).map (CFSG.KC.LQT.PW.imgW 64 (I.TF 0))

@[expose] noncomputable def HitV : List Nat :=
  (List.range 6).map (CFSG.KC.LQT.PW.imgW 64 (I.TF 1))

@[expose] noncomputable def AB8 : Array (Array Nat) :=
  #[Array.ofFn (n := 8330) fun i => ab 0 i.val, Array.ofFn (n := 8330) fun i => ab 1 i.val,
    Array.ofFn (n := 8330) fun i => ab 2 i.val, Array.ofFn (n := 8330) fun i => ab 3 i.val]

@[expose] noncomputable def RT8 : Array (Array Nat) :=
  (qp.map fun i => (slpTabsA (AB8.getD 0 #[]) (AB8.getD 1 #[]) prog)[i]!).toArray

@[expose] noncomputable def D8 : DcData where
  n := 8330
  B := B
  AB := AB8
  RT := RT8
  RTi := RT8.map invTab
  NR := 512
  rpar := (bfsEnumL 8330 B RT8 600).1
  rlab := (bfsEnumL 8330 B RT8 600).2
  lb := orbitLabels 8330 RT8
  reps := parseWords repsStr
  edges := parseEdges edgesStr
  c0 := root
  inEdge := parseNats inEdgeStr
  dIn := parseNats dInStr
  reach := (parseNats reachStr).toList
  outEdge := parseNats outEdgeStr
  dOut := parseNats dOutStr
  Vs := vData.map fun V =>
    let e := bfsEnumL 8330 B (RT8 ++ (V.1.map (tabW 8330 AB8)).toArray) (V.2 + 10)
    (V.1, e.1, e.2, V.2)
  order := 161280

end CFSG.KD.He589208

end
