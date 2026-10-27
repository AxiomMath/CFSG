module

public import Certificates.Kernel.J27031.D
public import Certificates.Kernel.J27031.T
public import Certificates.Data.Kernel.DcK

public section

namespace CFSG.KD.J27031

open CFSG.KC.DcK CFSG.KC.E64F CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.J2Cert

@[expose] noncomputable def im (c p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 c p

@[expose] def BK : List Nat := [0, 4, 3]

@[expose] def exOf (ab : Nat → Nat → Nat) (ws : List (List Nat)) (i : Nat) : Nat → Nat :=
  wordF ab (ws.getD i [])

@[expose] noncomputable def abc (l : Nat) : Nat := [S.TF 0, S.TF 1, P.TF 0, P.TF 1].getD l 0

@[expose] noncomputable def ab (l p : Nat) : Nat := im (abc l) p

@[expose] noncomputable def rtc (t : Nat) : Nat := [S.TF 155, S.TF 166, S.TF 179].getD t 0

@[expose] noncomputable def rt (t p : Nat) : Nat := im (rtc t) p

@[expose] noncomputable def rti (t p : Nat) : Nat := im (P.TF (t + 2)) p

@[expose] noncomputable def lbF (q : Nat) : Nat := im (P.TF 5) q

@[expose] noncomputable def QF (i : Nat) : Nat := im (P.TF 6) i

@[expose] noncomputable def vtF (q : Nat) : Nat := im (P.TF 7) q

@[expose] noncomputable def xt (j p : Nat) : Nat := im (X.TF j) p

@[expose] noncomputable def xti (j p : Nat) : Nat := im (X.TF (j + 63)) p

@[expose] noncomputable def ER : EnumK := recK 128 3 RR.TF

@[expose] noncomputable def EV0 : EnumK := recK 1152 3 V0.TF

@[expose] noncomputable def EV1 : EnumK := recK 1920 3 V1.TF

@[expose] def w0 : List (List Nat) := (vData.headD ([], 0)).1

@[expose] def w1 : List (List Nat) := ((vData.drop 1).headD ([], 0)).1

@[expose] noncomputable def K : DcK where
  n := 315
  B := BK
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
  order := 604800
  hpos j k := im (H.TF k) j

@[expose] noncomputable def IV : List Nat :=
  (List.range 63).map (CFSG.KC.LQT.PW.imgW 64 (I.TF 0))

@[expose] noncomputable def HitV : List Nat :=
  (List.range 63).map (CFSG.KC.LQT.PW.imgW 64 (I.TF 1))

@[expose] noncomputable def PN (i j k : Nat) : Nat := im (HN.TF (im (PI.TF 0) (i * 63 + j))) k

end CFSG.KD.J27031

end
