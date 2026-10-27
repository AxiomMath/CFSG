module

public import Certificates.Kernel.A45Cls.Cls
public import Certificates.Kernel.Parrott946.Cls
public import Certificates.Kernel.Parrott946.Grp17
public import Certificates.Data.Kernel.Parrott946.Clique

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.Parrott946
  CFSG.Certificates.Kernel.PkCV CertificateChecks.KernelA45

@[expose] noncomputable def wE (k : Nat) : Nat := lane (nat_lit 270) D17.WT k

@[expose] noncomputable def iE (j : Nat) : Nat := lane (nat_lit 270) D17.IT j

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp (nat_lit 45) (nat_lit 6) (mask 6) p q

@[expose] noncomputable def cmm (p q : Nat) : Bool := eq22 (nat_lit 45) (nat_lit 6) (mask 6) p q q p

@[expose] noncomputable def Ms : List Nat :=
  [D17.M0, D17.M1, D17.M2, D17.M3, D17.M4, D17.M5, D17.M6, D17.M7]

@[expose] noncomputable def sG : List Nat := [iE 6, iE 21, iE 31, iE 41]

theorem c17_words : bindWs 45 6 3 KA.G wE wW 0 = true := by decide +kernel

theorem c17_els : wW.take 10 = wA.take 10 ∧ Nat.beq (wE 10) (pk17 10) = true :=
  ⟨rfl, by decide +kernel⟩

theorem c17_binds : T0Z.G 0 = wE 1 ∧ T0Z.G 1 = wE 2 ∧ T0Z.G 2 = wE 5 ∧ T0Z.G 3 = wE 6 ∧
    T0Z.G 4 = wE 7 ∧ T0Z.G 5 = wE 8 ∧ bindWs 45 6 3 KA.G P3Z.G p3W 0 = true ∧
    KUV.G 0 = KA.G 0 ∧ KUV.G 1 = KA.G 1 ∧ KUV.G 2 = KA.G 2 ∧ KUV.T KUV.r0 = pc (wE 1) (wE 2) := by
  decide +kernel

theorem c17_orders : T0Z.N = 128 ∧ T0Z.ng = 6 ∧ P3Z.N = 81 ∧ P3Z.ng = 3 ∧ KUV.N = 36 ∧
    KUV.ng = 3 ∧ p3W.length = 3 ∧ wW.length = 49 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem c17_ids : T0Z.T 0 = pidn 45 6 ∧ P3Z.T 0 = pidn 45 6 := by decide +kernel

theorem c17_inv : ltChainK D17.I 0 = true ∧ lenK D17.I = 43 ∧ packL 270 D17.I = D17.IT ∧
    allL D17.I (fun _ x => bAnd(isInvK 45 6 x, memK 45 6 ps T0Z.N T0Z.T T0Z.S x)) 0 = true ∧
    cntN 128 (fun i => isInvK 45 6 (T0Z.T i)) = 43 := by
  decide +kernel

theorem c17_cm : cmK 45 6 D17.I D17.I D17.CM = true ∧ packL 43 D17.CM = D17.CMT := by
  decide +kernel

theorem c17_clique : cliqueK 43 D17.CMT Ms = true := by decide +kernel

theorem c17_masks : cntN 43 (bitB D17.M0) = 15 ∧ cntN 43 (bitB D17.M1) = 15 ∧
    cntN 43 (bitB D17.M2) = 15 ∧ cntN 43 (bitB D17.M3) = 15 ∧ cntN 43 (bitB D17.M4) = 7 ∧
    cntN 43 (bitB D17.M5) = 7 ∧ cntN 43 (bitB D17.M6) = 7 ∧ cntN 43 (bitB D17.M7) = 7 ∧
    strictB (pidn 45 6) (fun e => closedK 45 6 D17.I D17.M4 e &&
      closedK 45 6 D17.I D17.M5 e && closedK 45 6 D17.I D17.M6 e &&
      closedK 45 6 D17.I D17.M7 e) = true := by
  decide +kernel

theorem c17_gens : iE 6 = wE 1 ∧ iE 21 = pc (wE 5) (wE 7) ∧ iE 31 = pc (wE 6) (wE 8) ∧
    iE 41 = wE 0 ∧ iE 25 = pc (wE 1) (wE 2) ∧ iE 38 = pc (pc (wE 5) (wE 6)) (wE 8) ∧
    iE 11 = wE 2 ∧ iE 12 = pc (wE 2) (wE 5) ∧ iE 14 = pc (pc (wE 1) (wE 6)) (wE 8) := by
  decide +kernel

@[expose] noncomputable def spanOK (js : List Nat) (m : Nat) : Bool :=
  Nat.beq (coverK 43 D17.I (pidn 45 6) (spanK 45 6 (pidn 45 6) (mapK iE js)))
    (Nat.lor m (Nat.shiftLeft 1 43))

theorem c17_spans : spanOK [6, 21, 31, 41] D17.M0 = true ∧ spanOK [25, 21, 38, 41] D17.M1 = true ∧
    spanOK [11, 6, 41, 21] D17.M2 = true ∧ spanOK [12, 14, 41, 21] D17.M3 = true := by
  decide +kernel

@[expose] noncomputable def centOK (js : List Nat) (m : Nat) : Bool :=
  strictB (List.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 43) 1)
      (fun j _ ih => Nat.land (lane 43 D17.CMT j) ih) js) fun c => Nat.beq (Nat.land c m) c

theorem c17_ecent : centOK [6, 21, 31, 41] D17.M0 = true ∧ centOK [25, 21, 38, 41] D17.M1 = true ∧
    centOK [11, 6, 41, 21] D17.M2 = true ∧ centOK [12, 14, 41, 21] D17.M3 = true := by
  decide +kernel

theorem c17_t0span : idxCoverK 45 6 ps 128 T0Z.T T0Z.S
    (spanK 45 6 (pidn 45 6) [wE 1, wE 2, wE 0, wE 5, wE 6, wE 7, wE 8]) =
      Nat.sub (Nat.shiftLeft 1 128) 1 := by
  decide +kernel

theorem c17_zc : zcK 45 6 6 128 T0Z.G T0Z.T (wE 0) = true ∧
    allN 6 (fun k => cmm (wE 0) (T0Z.G k)) = true := by
  decide +kernel

@[expose] noncomputable def rE (i : Nat) : Nat := wE (Nat.add 12 i)

@[expose] noncomputable def rI (i : Nat) : Nat := wE (Nat.add 21 i)

theorem c17_cos : eqP 45 6 (rE 0) (pidn 45 6) = true ∧
    allN 9 (fun i => bAnd(eqP 45 6 (pc (rE i) (rI i)) (pidn 45 6), cmm (rE i) (wE 0))) = true ∧
    allN 9 (fun i => allN 9 fun j => !Nat.blt i j ||
      !memK 45 6 ps T0Z.N T0Z.T T0Z.S (pc (rE j) (rI i))) = true ∧
    allN 8 (fun i => !allN 6 fun k =>
      memK 45 6 ps T0Z.N T0Z.T T0Z.S (pc (rE (Nat.succ i)) (pc (T0Z.G k) (rI (Nat.succ i))))) =
      true := by
  decide +kernel

theorem c17_ns : strictB (pidn 45 6) (fun e =>
    ((allN 6 fun k => normMaskK 45 6 D17.I D17.M0 e (T0Z.G k) sG) &&
      normMaskK 45 6 D17.I D17.M0 e (rE 5) sG && normMaskK 45 6 D17.I D17.M0 e (rE 6) sG &&
      !normMaskK 45 6 D17.I D17.M0 e (rE 1) sG && !normMaskK 45 6 D17.I D17.M0 e (rE 2) sG &&
      !normMaskK 45 6 D17.I D17.M0 e (rE 3) sG && !normMaskK 45 6 D17.I D17.M0 e (rE 4) sG &&
      !normMaskK 45 6 D17.I D17.M0 e (rE 7) sG && !normMaskK 45 6 D17.I D17.M0 e (rE 8) sG)) =
    true := by
  decide +kernel

theorem c17_cs : strictB (pidn 45 6) (fun e =>
    allN 128 fun i => allL [rE 0, rE 5, rE 6] (fun _ r => strictB (pc (T0Z.T i) r) fun x =>
      !allL sG (fun _ g => cmm x g) 0 || inMaskK D17.I D17.M0 e x) 0) = true := by
  decide +kernel

@[expose] noncomputable def orbRec (e f z rc : Nat) : Bool :=
  strictB (Nat.land rc 63) fun j => strictB (Nat.shiftRight rc 6) fun k =>
    bitB D17.M0 j && Nat.beq (fixK 45 6 (iE j)) f &&
      eq22 45 6 (mask 6) (wE k) z (iE j) (wE k) && normMaskK 45 6 D17.I D17.M0 e (wE k) sG

theorem c17_orb : cntN 43 (fun j => bitB D17.M0 j && Nat.beq (fixK 45 6 (iE j)) 13) = 5 ∧
    cntN 43 (fun j => bitB D17.M0 j && Nat.beq (fixK 45 6 (iE j)) 5) = 10 ∧
    ltChainK (mapK (fun rc => Nat.succ (Nat.land rc 63)) t5R) 0 = true ∧
    ltChainK (mapK (fun rc => Nat.succ (Nat.land rc 63)) f5R) 0 = true ∧
    strictB (pidn 45 6) (fun e => allL t5R (fun _ rc => orbRec e 13 (wE 0) rc) 0 &&
      allL f5R (fun _ rc => orbRec e 5 (pc (wE 1) (wE 0)) rc) 0) = true ∧
    spanOK [1, 6, 8, 15, 41] D17.M0 = true ∧ lenK t5R = 5 ∧ lenK f5R = 10 := by
  decide +kernel

@[expose] noncomputable def meetK (z : Nat) : Bool :=
  allL meetR (fun i rc => strictB (Nat.land rc 63) fun j =>
    strictB (Nat.shiftRight rc 6) fun k => bitB D17.M0 j && bitB (lane 64 (packL 64 Ms) i) j &&
      eq22 45 6 (mask 6) (wE k) (iE j) z (wE k)) 0

theorem c17_meet : meetK (pc (wE 1) (wE 0)) = true ∧ lenK meetR = 4 := by decide +kernel

theorem c17_fix : isInvK 45 6 (pc (wE 1) (wE 0)) = true ∧ isInvK 45 6 (pc (wE 1) (wE 2)) = true ∧
    fixK 45 6 (pc (wE 1) (wE 0)) = 5 ∧ fixK 45 6 (pc (wE 1) (wE 2)) = 15 := by
  decide +kernel

theorem c17_b5 : strictB (wE 10) (fun b => strictB (pc b b) fun b2 =>
    strictB (pc (wE 1) (wE 2)) fun uv =>
      eqP 45 6 (pc (pc b2 b2) b) (pidn 45 6) && !eqP 45 6 b (pidn 45 6) && cmm b uv &&
        eq22 45 6 (mask 6) (wE 11) b b2 (wE 11) && cmm (wE 0) uv) = true := by
  decide +kernel

theorem c17_kuv : strictB (wE 10) (fun b => strictB (pc (wE 1) (wE 2)) fun uv =>
    allN 36 fun i => !cmm (KUV.T i) b || Nat.beq (KUV.T i) uv) = true := by
  decide +kernel

@[expose] noncomputable def ord3K (P : Nat) : Bool :=
  strictB (pc P P) fun p2 => bAnd(isIdK 45 6 (pc P p2), !isIdK 45 6 P)

theorem c17_p3 : allN 81 (fun i => strictB (P3Z.T i) fun p => !ord3K p ||
    memK 45 6 ps K1.N K1.T K1.S p || memK 45 6 ps K12.N K12.T K12.S p ||
      memK 45 6 ps K12i.N K12i.T K12i.S p) = true := by
  decide +kernel

@[expose] noncomputable def q8K (k : List Nat → Bool) : Bool :=
  strictB (wE 7) fun a => strictB (wE 8) fun b => strictB (pc a a) fun a2 =>
    strictB (pc a2 a) fun a3 => strictB (pidn 45 6) fun e => strictB (pc b a) fun ba =>
      strictB (pc b a2) fun ba2 => strictB (pc b a3) fun ba3 => k [e, a, a2, a3, b, ba, ba2, ba3]

@[expose] noncomputable def d8K (k : List Nat → Bool) : Bool :=
  strictB (pc (wE 0) (pc (wE 2) (wE 9))) fun r => strictB (wE 0) fun s =>
    strictB (pc r r) fun r2 => strictB (pc r2 r) fun r3 => strictB (pidn 45 6) fun e =>
      strictB (pc s r) fun sr => strictB (pc s r2) fun sr2 => strictB (pc s r3) fun sr3 =>
        k [e, r, r2, r3, s, sr, sr2, sr3]

theorem c17_q8 : q8K (fun L => mulClosedK 45 6 L && distinctK L) = true := by decide +kernel

theorem c17_d8 : d8K (fun L => mulClosedK 45 6 L && distinctK L &&
    anyL L (fun _ x => Nat.beq x (wE 1)) 0 && anyL L (fun _ x => Nat.beq x (pc (wE 2) (wE 9))) 0 &&
    strictB (pc (wE 2) (wE 9)) fun vb => strictB (pc (wE 1) (wE 0)) fun ut =>
      allL L (fun _ x => !(cmm x (wE 0) && cmm x (wE 1) && cmm x vb) ||
        eqP 45 6 x (pidn 45 6) || Nat.beq x ut) 0) = true := by
  decide +kernel

theorem c17_rels : strictB (pc (wE 2) (wE 9)) (fun vb => strictB (pc (wE 1) (wE 0)) fun ut =>
    strictB (pc (wE 1) (wE 2)) fun uv => strictB (pc (wE 4) (wE 4)) fun s22 =>
      eq22 45 6 (mask 6) (wE 7) (pc (wE 8) (wE 7)) (wE 8) (pidn 45 6) && cmm (wE 7) (wE 3) &&
        cmm (wE 8) (wE 3) && eqP 45 6 (pc s22 (wE 4)) (pidn 45 6) && cmm uv (pc (wE 3) s22) &&
        eqP 45 6 (pc vb vb) (pidn 45 6) && strictB (pc (wE 0) vb) (fun tv => eqP 45 6 (pc tv tv) ut) &&
        cmm ut vb && cmm vb (pc (wE 3) (wE 4))) = true := by
  decide +kernel

end CertificateChecks.Parrott946

end
