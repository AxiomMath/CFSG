module

public import Certificates.Data.Kernel.J4Q.ZFr
public import Certificates.Data.Kernel.J4Q.ZFrData
public import Certificates.Data.Kernel.J4Q.Pack
public import Certificates.Kernel.J4Q.ZFrPk
public import Certificates.Kernel.J4Q.QT2A
public import Certificates.Kernel.J4Q.EtaMats
public import Certificates.Kernel.J4Q.X0OrbData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZB336Native

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

@[expose] noncomputable def zfSeqB (s : List Nat) : Nat :=
  s.foldr (fun g acc => compB (ZGB.getD g 0) acc) ZIDB

@[expose] noncomputable def zfConsB (VsB : List Nat) (bs : List Nat) (P : Nat) : Bool :=
  bs.all fun bj => bs.all fun bl => VsB.all fun v =>
    actB v bj != bl || actB P bl == actB v (actB P bj)

@[expose] noncomputable def zfBtGoB (TsB VsB : List Nat) :
    List (List (List Nat)) → List Nat → List Nat → Nat → List Nat → List (List Nat)
  | [], _, _, P, tup => if TsB.all (fun T => compB P T == compB T P) then [tup.reverse] else []
  | lv :: C, b :: base, bs, P, tup => (List.range lv.length).flatMap fun t =>
      (fun P2 => if zfConsB VsB (bs ++ [b]) P2 then zfBtGoB TsB VsB C base (bs ++ [b]) P2 (t :: tup)
        else []) (compB P (zfSeqB (lv.getD t [])))
  | _ :: _, [], _, _, _ => []

@[expose] noncomputable def zfMasksB (TsB : List Nat) (d : List Nat) : List Nat :=
  (List.range 2048).filter fun c =>
    (List.range 4).all fun i => (c ^^^ actB (TsB.getD i 0) c) == d.getD i 0

@[expose] noncomputable def gwK (w : List Int) : Nat := wordJ c rm one G5 G5i w

@[expose] noncomputable def conjByK (gw : List Int) (T : Nat) : Nat :=
  mulJ c rm (mulJ c rm (gwK gw) T) (gwK (invW gw))

@[expose] noncomputable def cjRowsK (T : Nat) : Nat → Nat
  | 0 => T
  | n + 1 => mulJ c rm (mulJ c rm (getN one XG 0) (cjRowsK T n)) (getN one XG 8)

@[expose] noncomputable def msK (T0 : Nat) (gw : List Int) : Nat → Nat
  | 0 => CFSG.KD.ETA.EF 1
  | n + 1 => conjByK gw (cjRowsK T0 (n + 1))

@[expose] noncomputable def prodK : List Nat → Nat
  | [] => one
  | r :: rs => mulJ c rm r (prodK rs)

@[expose] noncomputable def tabOKK (M : Nat) (T : List Nat) : Bool :=
  lenOK T && (List.range 11).all fun j =>
    Nat.beq (mulJ c rm (mulJ c rm M (CFSG.KD.ETA.EF (2 ^ j))) M) (CFSG.KD.ETA.EF (T.getD j 0))

@[expose] noncomputable def seqRK (s : List Nat) : Nat :=
  s.foldr (fun g acc => mulJ c rm (gwK (zcGenWords.getD g [])) acc) one

@[expose] noncomputable def seqRiK (s : List Nat) : Nat :=
  s.foldl (fun acc g => mulJ c rm (gwK (invW (zcGenWords.getD g []))) acc) one

@[expose] noncomputable def zfLightK (T0 : Nat) (gw : List Int) (Ts : List (List Nat)) : Bool :=
  Ts.length == 4 && Nat.beq (conjByK gw T0) (CFSG.KD.ETA.EF 1) &&
    (List.finRange 4).all (fun i => Nat.beq (mulJ c rm (msK T0 gw i) (msK T0 gw i)) one &&
      tabOKK (msK T0 gw i) (Ts.getD i [])) &&
    (List.finRange 4).all (fun i => (List.finRange 4).all fun j =>
      Nat.beq (mulJ c rm (msK T0 gw i) (msK T0 gw j)) (mulJ c rm (msK T0 gw j) (msK T0 gw i))) &&
    (List.finRange 4).all fun i =>
      Nat.beq (mulJ c rm (mulJ c rm (conjByK gw (getN one XG 0)) (msK T0 gw i)) (conjByK gw (getN one XG 8)))
        (prodK ((zS i).map fun j => msK T0 gw j))

@[expose] noncomputable def zfSurvK (T0 : Nat) (gw : List Int) (TsB : List Nat) (C : List (List (List Nat)))
    (surv sq D : List (List Nat)) (E : List Nat) (u : Nat) : Bool :=
  (sq.getD u []).all (· < 3) && (D.getD u []).all (· < 2048) && decide (E.getD u 0 < 2048) &&
    zfSeqT (sq.getD u []) == zfP C (surv.getD u []) &&
    (List.finRange 4).all (fun i =>
      Nat.beq (mulJ c rm (mulJ c rm (mulJ c rm (msK T0 gw i) (seqRK (sq.getD u []))) (msK T0 gw i))
        (seqRiK (sq.getD u []))) (CFSG.KD.ETA.EF ((D.getD u []).getD i 0))) &&
    ((zfMasksB TsB (D.getD u [])).isEmpty ||
      (Nat.beq (mulJ c rm (seqRK (sq.getD u [])) (seqRK (sq.getD u []))) (CFSG.KD.ETA.EF (E.getD u 0)) &&
        (zfMasksB TsB (D.getD u [])).all fun c' =>
          (c' ^^^ actT (zfSeqT (sq.getD u [])) c') == E.getD u 0))

@[expose] noncomputable def zfIB (TsB : List Nat) (surv D : List (List Nat)) : List (Nat × Nat) :=
  (List.range surv.length).flatMap fun u => (zfMasksB TsB (D.getD u [])).map fun c' => (u, c')

@[expose] noncomputable def zfCountK (gw : List Int) (TsB : List Nat) (surv sq D : List (List Nat)) (k : Nat) :
    Bool :=
  decide (((zfIB TsB surv D).filter fun q =>
      Nat.beq (mulJ c rm (mulJ c rm (CFSG.KD.ETA.EF q.2) (seqRK (sq.getD q.1 []))) (conjByK gw (getN one XG 0)))
        (mulJ c rm (conjByK gw (getN one XG 0)) (mulJ c rm (CFSG.KD.ETA.EF q.2) (seqRK (sq.getD q.1 []))))).length
      ≤ k) &&
    decide (16 * k < (zfIB TsB surv D).length)

@[expose] noncomputable def t0K (e : Nat) : Nat := mulJ c rm (CFSG.KD.ETA.EF e) (gwK zB336Word)

@[expose] noncomputable def zfStatK (Ts : List (List Nat)) (TsB VsB : List Nat) (base : List Nat)
    (C : List (List (List Nat))) (surv sq D : List (List Nat)) : Bool :=
  Ts == TsB.map unpackP && TsB.length == 4 && zfVs Ts == VsB.map unpackP &&
    zfChainOK C base && (C.map List.length).prod == 887040 && surv.length == 32 &&
    sq.length == surv.length && D.length == surv.length &&
    decide ((List.range surv.length).map fun u => zfSeqT (sq.getD u [])).Nodup

@[expose] noncomputable def zfPart (e : Nat) (gw : List Int) (Ts : List (List Nat)) (TsB VsB : List Nat)
    (base : List Nat) (C : List (List (List Nat))) (surv sq D : List (List Nat)) (E : List Nat) :
    Nat → Bool
  | 0 => zfLightK (t0K e) gw Ts
  | 1 => zfStatK Ts TsB VsB base C surv sq D
  | 2 => zfBtGoB TsB VsB C base [] ZIDB [] == surv
  | 7 => zfCountK gw TsB surv sq D 4
  | p => (List.range 8).all fun i => zfSurvK (t0K e) gw TsB C surv sq D E (8 * (p - 3) + i)

@[expose] noncomputable def zfFamA : Nat → Bool :=
  zfPart 37 zGwB336a zfTsA ZTsBA ZVsBA zfBaseA zfTrA zfSurvA zfSqA zfDA zfEA

@[expose] noncomputable def zfFamB : Nat → Bool :=
  zfPart 97 zGwB336b zfTsB ZTsBB ZVsBB zfBaseB zfTrB zfSurvB zfSqB zfDB zfEB

@[expose] noncomputable def zfFamC : Nat → Bool :=
  zfPart 236 zGwB336c zfTsC ZTsBC ZVsBC zfBaseC zfTrC zfSurvC zfSqC zfDC zfEC

@[expose] noncomputable def zfFamD : Nat → Bool :=
  zfPart 491 zGwB336d zfTsD ZTsBD ZVsBD zfBaseD zfTrD zfSurvD zfSqD zfDD zfED

end CertificateChecks.KernelJ4Q

end
