module

public import Certificates.Kernel.TwoHS.HarCD
public import Certificates.Kernel.TwoHS.HYOps
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Spor.MulHQI
public import Certificates.Data.Kernel.Spor.PEnumC
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PinvSSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def cnK (p : Nat) : Bool := canonK 11200 14 (mask 14) (11200 * 14) p

@[expose] noncomputable def pinvY (p : Nat) : Nat := pinvS 11200 14 (mask 14) p

@[expose] noncomputable def invYK (p r : Nat) : Bool :=
  bAnd(cnK p, bAnd(cnK r, invEqK 11200 14 (mask 14) (11200 * 14) p r))

theorem pinvS_eq_of_permOK {n w p r : Nat} (hw : n < 2 ^ w)
    (hp : canonK n w (mask w) (n * w) p = true) (hr : canonK n w (mask w) (n * w) r = true)
    (hpr : permOK n w (mask w) (n * w) p r = true) : pinvS n w (mask w) p = r := by
  obtain ⟨-, -, -, hlt⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, hw1, hr0, -⟩ := CFSG.KS.PF.canon_facts hr
  unfold permOK at hpr
  simp only [bAnd_iff] at hpr
  obtain ⟨-, -, ha⟩ := hpr
  have key : ∀ i < n, pg w (mask w) r (pg w (mask w) p i) = i := fun i hi => by
    have hi' := CFSG.KS.Raw.Orb.allN_iff.1 ha i hi
    rw [CFSG.KS.PF.strictB_eqP, bAnd_iff] at hi'
    exact Nat.eq_of_beq_eq_true hi'.2
  have hinj : CFSG.KS.PinvS.InjK n w p :=
    ⟨hlt, fun a ha' b hb e => by rw [← key a ha', ← key b hb, e]⟩
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw1) (CFSG.KS.PinvS.pinvS_shr hw hlt) hr0
    fun j hj => ?_
  obtain ⟨i, hi, rfl⟩ := CFSG.KS.PinvS.surj_of_injK hinj j hj
  rw [CFSG.KS.PinvS.pg_pinvS hw hinj hi, key i hi]

theorem pinvY_eq {p r : Nat} (hp : cnK p = true) (hr : cnK r = true)
    (hpr : invEqK 11200 14 (mask 14) (11200 * 14) p r = true) : pinvY p = r :=
  pinvS_eq_of_permOK (by decide) hp hr hpr

@[expose] noncomputable def G3K : Nat := WK harCW3

@[expose] noncomputable def G5K : Nat := WK harCW5

@[expose] noncomputable def CK : Nat := WK harCWit

@[expose] noncomputable def CKI : Nat := pinvY CK

@[expose] noncomputable def Z1K : Nat := UK [3, 3, 3, 3]

@[expose] noncomputable def C0K : Nat := UK [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]

@[expose] noncomputable def Z2K : Nat := pc C0K Z1K

@[expose] noncomputable def commP (a b : Nat) : Nat := pc (pc a b) (pc (pinvY a) (pinvY b))

@[expose] noncomputable def QK (j : Nat) : Nat :=
  commP (UK (harCQPairs.getD j ([], true)).1) (cond (harCQPairs.getD j ([], true)).2 G3K G5K)

@[expose] noncomputable def CGK (j : Nat) : Nat := [UL 1, UL 2, UL 3, G3K, G5K].getD j 0

theorem harC_u0 : Nat.beq (TE.GI 0) (UL 1) = true := by
  quickRfl

theorem harC_u1 : Nat.beq (TE.GI 1) (UL 2) = true := by
  quickRfl

theorem harC_u2 : Nat.beq (TE.GI 2) (UL 3) = true := by
  quickRfl

@[expose] noncomputable def harCSU (l : Nat) : Nat :=
  nIf(Nat.beq l 1, TE.GI 0, nIf(Nat.beq l 2, TE.GI 1, nIf(Nat.beq l 3, TE.GI 2, UL l)))

theorem harC_SU : UL = harCSU := by
  funext l
  match l with
  | 0 => rfl
  | 1 => exact (Nat.eq_of_beq_eq_true harC_u0).symm
  | 2 => exact (Nat.eq_of_beq_eq_true harC_u1).symm
  | 3 => exact (Nat.eq_of_beq_eq_true harC_u2).symm
  | _ + 4 => rfl

@[expose] noncomputable def harCUKr (wd : List Nat) : Nat := wfoldK 11200 14 (mask 14) harCSU wd idK

theorem harC_UK : UK = harCUKr := by
  funext wd
  unfold UK harCUKr
  rw [harC_SU]

theorem harC_Z1 : Z1K = harCUKr [3, 3, 3, 3] := by
  unfold Z1K
  rw [harC_UK]

theorem harC_C0 : C0K = harCUKr [1, 2, 1, 2, 3, 1, 2, 1, 2, 3] := by
  unfold C0K
  rw [harC_UK]

theorem harC_z1e : Nat.beq (TE.T 88) (harCUKr [3, 3, 3, 3]) = true := by
  quickRfl

theorem harC_Z1T : Z1K = TE.T 88 := by
  rw [harC_Z1]
  exact (Nat.eq_of_beq_eq_true harC_z1e).symm

theorem harC_c0e : Nat.beq (TE.T 1003) (harCUKr [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) = true := by
  quickRfl

theorem harC_C0T : C0K = TE.T 1003 := by
  rw [harC_C0]
  exact (Nat.eq_of_beq_eq_true harC_c0e).symm

theorem harC_invU : invYK =
    fun p r => bAnd(cnK p, bAnd(cnK r, invEqK 11200 14 (mask 14) (11200 * 14) p r)) :=
  rfl

theorem harC_invG {c : Nat → Bool} {e f : Nat → Nat → Bool}
    (hf : f = fun p r => bAnd(c p, bAnd(c r, e p r))) {p r : Nat} (hp : c p = true)
    (hr : c r = true) (h : e p r = true) : f p r = true := by
  subst hf
  exact (bAnd_iff _ _).2 ⟨hp, (bAnd_iff _ _).2 ⟨hr, h⟩⟩

theorem harC_ck : (cnK CK && invEqK 11200 14 (mask 14) (11200 * 14) CK CK) = true := by
  quickRfl

theorem harC_CKI : CKI = CK := by
  have h := harC_ck
  simp only [Bool.and_eq_true] at h
  exact pinvY_eq h.1 h.1 h.2

theorem harC_CGK : CGK = fun j => [harCSU 1, harCSU 2, harCSU 3, G3K, G5K].getD j 0 := by
  funext j
  unfold CGK
  rw [harC_SU]

theorem harC_g3 : Nat.beq (TCG 3) G3K = true := by
  quickRfl

theorem harC_g4 : Nat.beq (TCG 4) G5K = true := by
  quickRfl

theorem harC_tG3 : TCG 3 = G3K := Nat.eq_of_beq_eq_true harC_g3

theorem harC_tG5 : TCG 4 = G5K := Nat.eq_of_beq_eq_true harC_g4

@[expose] noncomputable def harCQKr (j : Nat) : Nat :=
  commP (harCUKr (harCQPairs.getD j ([], true)).1)
    (cond (harCQPairs.getD j ([], true)).2 (TCG 3) (TCG 4))

theorem harC_QK : QK = harCQKr := by
  funext j
  unfold QK harCQKr
  rw [harC_UK, harC_tG3, harC_tG5]

theorem harC_b01 : allN 3 (fun j => bAnd(Nat.beq (TE.GI j) (UL (Nat.succ j)),
    bAnd(Nat.beq (TE.G j) idK, invYK (TE.GI j) (TEI j)))) = true := by
  rw [harC_SU]
  quickRfl

theorem harC_b02 : Nat.beq TE.cnt 1024 = true := by
  quickRfl

theorem harC_b03 : penumHdK idK TE.cnt 2000 TE.T TE.PL = true := by
  quickRfl

theorem harC_b05 : Nat.beq TQ.cnt 128 = true := by
  quickRfl

theorem harC_b06 : penumHdK idK TQ.cnt 400 TQ.T TQ.PL = true := by
  quickRfl

theorem harC_b07 : allN 5 (fun j => bAnd(Nat.beq (TCG j) (CGK j), invYK (TCG j) (TCGI j))) = true := by
  rw [harC_CGK, ← harC_tG3, ← harC_tG5]
  quickRfl

theorem harC_tc : (cnK (TCG 3) && (cnK (TCGI 3) &&
    (invEqK 11200 14 (mask 14) (11200 * 14) (TCG 3) (TCGI 3) && (cnK (TCG 4) && (cnK (TCGI 4) &&
    invEqK 11200 14 (mask 14) (11200 * 14) (TCG 4) (TCGI 4)))))) = true := by
  quickRfl

theorem harC_invB (c : Bool) : pinvY (cond c (TCG 3) (TCG 4)) = cond c (TCGI 3) (TCGI 4) := by
  have h := harC_tc
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases c
  · exact pinvY_eq h4 h5 h6
  · exact pinvY_eq h1 h2 h3

@[expose] noncomputable def harCQK (j : Nat) : Nat := [904, 1, 1, 925, 925, 142].getD j 0

@[expose] noncomputable def harCQA (wd : List Nat) (k : Nat) : Bool :=
  Nat.beq (harCUKr wd) (TE.T k) &&
    (cnK (TE.T k) && invEqK 11200 14 (mask 14) (11200 * 14) (TE.T k) (TE.T k))

@[expose] noncomputable def harCQC (j k : Nat) : Bool :=
  Nat.beq (TQ.GI j) (pc (pc (TE.T k) (cond (harCQPairs.getD j ([], true)).2 (TCG 3) (TCG 4)))
    (pc (TE.T k) (cond (harCQPairs.getD j ([], true)).2 (TCGI 3) (TCGI 4))))

@[expose] noncomputable def harCQT (j : Nat) : Bool :=
  Nat.beq (TQ.G j) idK && invYK (TQ.GI j) (TQI j)

theorem harC_a0 : harCQA (harCQPairs.getD 0 ([], true)).1 (harCQK 0) = true := by
  quickRfl

theorem harC_a1 : harCQA (harCQPairs.getD 1 ([], true)).1 (harCQK 1) = true := by
  quickRfl

theorem harC_a3 : harCQA (harCQPairs.getD 3 ([], true)).1 (harCQK 3) = true := by
  quickRfl

theorem harC_a5 : harCQA (harCQPairs.getD 5 ([], true)).1 (harCQK 5) = true := by
  quickRfl

theorem harC_q0 : harCQC 0 (harCQK 0) = true := by
  quickRfl

theorem harC_q1 : harCQC 1 (harCQK 1) = true := by
  quickRfl

theorem harC_q2 : harCQC 2 (harCQK 2) = true := by
  quickRfl

theorem harC_q3 : harCQC 3 (harCQK 3) = true := by
  quickRfl

theorem harC_q4 : harCQC 4 (harCQK 4) = true := by
  quickRfl

theorem harC_q5 : harCQC 5 (harCQK 5) = true := by
  quickRfl

theorem harC_aF : ∀ j < 6, harCQA (harCQPairs.getD j ([], true)).1 (harCQK j) = true
  | 0, _ => harC_a0
  | 1, _ => harC_a1
  | 2, _ => harC_a1
  | 3, _ => harC_a3
  | 4, _ => harC_a3
  | 5, _ => harC_a5
  | _ + 6, h => absurd h (by omega)

theorem harC_t0 : harCQT 0 = true := by
  quickRfl

theorem harC_t1 : harCQT 1 = true := by
  quickRfl

theorem harC_t2 : harCQT 2 = true := by
  quickRfl

theorem harC_t3 : harCQT 3 = true := by
  quickRfl

theorem harC_t4 : harCQT 4 = true := by
  quickRfl

theorem harC_t5 : harCQT 5 = true := by
  quickRfl

theorem harC_qF {j k : Nat} (ha : harCQA (harCQPairs.getD j ([], true)).1 k = true)
    (h : harCQC j k = true) (ht : harCQT j = true) :
    bAnd(Nat.beq (TQ.GI j) (QK j), bAnd(Nat.beq (TQ.G j) idK, invYK (TQ.GI j) (TQI j))) = true := by
  unfold harCQA at ha
  unfold harCQT at ht
  simp only [Bool.and_eq_true] at ha ht
  obtain ⟨he, hk, hkk⟩ := ha
  obtain ⟨hg, hi⟩ := ht
  refine (bAnd_iff _ _).2 ⟨?_, (bAnd_iff _ _).2 ⟨hg, hi⟩⟩
  rw [harC_QK]
  unfold harCQKr commP
  rw [Nat.eq_of_beq_eq_true he, pinvY_eq hk hk hkk, harC_invB]
  exact h

theorem harC_b04 : allN 6 (fun j => bAnd(Nat.beq (TQ.GI j) (QK j),
    bAnd(Nat.beq (TQ.G j) idK, invYK (TQ.GI j) (TQI j)))) = true := by
  have key : ∀ j < 6, harCQC j (harCQK j) = true ∧ harCQT j = true := fun j hj =>
    match j, hj with
    | 0, _ => ⟨harC_q0, harC_t0⟩
    | 1, _ => ⟨harC_q1, harC_t1⟩
    | 2, _ => ⟨harC_q2, harC_t2⟩
    | 3, _ => ⟨harC_q3, harC_t3⟩
    | 4, _ => ⟨harC_q4, harC_t4⟩
    | 5, _ => ⟨harC_q5, harC_t5⟩
    | _ + 6, h => absurd h (by omega)
  exact CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => harC_qF (harC_aF j hj) (key j hj).1 (key j hj).2

theorem harC_b08 : Nat.blt (r32 TQR 0) TQ.cnt = true := by
  quickRfl

theorem harC_b09 : Nat.beq (TQ.T (r32 TQR 0)) (UK harCRoot) = true := by
  rw [harC_UK]
  quickRfl

theorem harC_b10 : Nat.beq (pc (UK harCRoot) (UK harCRoot)) Z1K = true := by
  rw [← Nat.eq_of_beq_eq_true harC_b09, harC_Z1T]
  quickRfl

theorem harC_b11 : Nat.beq (pc (pc G3K G3K) G3K) idK = true := by
  rw [← harC_tG3]
  quickRfl

theorem harC_b12 : bIf(Nat.beq G3K idK, false, true) = true := by
  rw [← harC_tG3]
  quickRfl

theorem harC_b13 : Nat.beq (pc (pc (pc (pc G5K G5K) G5K) G5K) G5K) idK = true := by
  rw [← harC_tG5]
  quickRfl

theorem harC_b14 : bIf(Nat.beq G5K idK, false, true) = true := by
  rw [← harC_tG5]
  quickRfl

theorem harC_b15 : Nat.beq (pc G3K Z1K) (pc Z1K G3K) = true := by
  rw [harC_Z1T, ← harC_tG3]
  quickRfl

theorem harC_b16 : Nat.beq (pc G5K Z1K) (pc Z1K G5K) = true := by
  rw [harC_Z1T, ← harC_tG5]
  quickRfl

theorem harC_b17 : Nat.beq (pc CK Z1K) (pc Z1K CK) = true := by
  rw [harC_Z1T]
  quickRfl

theorem harC_b18 : invYK CK CKI = true := by
  have h := harC_ck
  simp only [Bool.and_eq_true] at h
  rw [harC_CKI]
  exact harC_invG (c := cnK) (e := invEqK 11200 14 (mask 14) (11200 * 14)) harC_invU h.1 h.1 h.2

theorem harC_b19 : cnK Z1K = true := by
  rw [harC_Z1T]
  quickRfl

theorem harC_b20 : cnK C0K = true := by
  rw [harC_C0T]
  quickRfl

theorem harC_base : bAnd(allN 3 (fun j => bAnd(Nat.beq (TE.GI j) (UL (Nat.succ j)),
    bAnd(Nat.beq (TE.G j) idK, invYK (TE.GI j) (TEI j)))),
  bAnd(Nat.beq TE.cnt 1024, bAnd(penumHdK idK TE.cnt 2000 TE.T TE.PL,
  bAnd(allN 6 (fun j => bAnd(Nat.beq (TQ.GI j) (QK j),
    bAnd(Nat.beq (TQ.G j) idK, invYK (TQ.GI j) (TQI j)))),
  bAnd(Nat.beq TQ.cnt 128, bAnd(penumHdK idK TQ.cnt 400 TQ.T TQ.PL,
  bAnd(allN 5 (fun j => bAnd(Nat.beq (TCG j) (CGK j), invYK (TCG j) (TCGI j))),
  bAnd(Nat.blt (r32 TQR 0) TQ.cnt, bAnd(Nat.beq (TQ.T (r32 TQR 0)) (UK harCRoot),
  bAnd(Nat.beq (pc (UK harCRoot) (UK harCRoot)) Z1K,
  bAnd(Nat.beq (pc (pc G3K G3K) G3K) idK, bAnd(bIf(Nat.beq G3K idK, false, true),
  bAnd(Nat.beq (pc (pc (pc (pc G5K G5K) G5K) G5K) G5K) idK, bAnd(bIf(Nat.beq G5K idK, false, true),
  bAnd(Nat.beq (pc G3K Z1K) (pc Z1K G3K), bAnd(Nat.beq (pc G5K Z1K) (pc Z1K G5K),
  bAnd(Nat.beq (pc CK Z1K) (pc Z1K CK), bAnd(invYK CK CKI, bAnd(cnK Z1K, cnK C0K))))))))))))))))))) =
    true := by
  rw [harC_b01, harC_b02, harC_b03, harC_b04, harC_b05, harC_b06, harC_b07, harC_b08, harC_b09,
    harC_b10, harC_b11, harC_b12, harC_b13, harC_b14, harC_b15, harC_b16, harC_b17, harC_b18,
    harC_b19, harC_b20]

@[expose] noncomputable def peE (k : Nat) : Bool :=
  penumSlK 11200 14 (mask 14) (11200 * 14) true TE.G TE.GI 3 TE.cnt TE.T TE.PL TE.POS TE.SRT TE.SRI
    (Nat.mul 32 k) 32

@[expose] noncomputable def hsE (k : Nat) : Bool :=
  slK TE.cnt (hsortPtK 11200 14 (mask 14) TE.cnt TE.T TE.HS TE.HSI) (Nat.mul 64 k) 64

@[expose] noncomputable def peQ (k : Nat) : Bool :=
  CFSG.KS.PEnumC.penumSlC 6 12 TQ.cnt TQ.T TQ.PL TQ.POS TQCl TQ.SRT TQ.SRI (Nat.mul 64 k) 64

@[expose] noncomputable def hsQ (k : Nat) : Bool :=
  slK TQ.cnt (hsortPtK 11200 14 (mask 14) TQ.cnt TQ.T TQ.HS TQ.HSI) (Nat.mul 64 k) 64

@[expose] noncomputable def nqQ (k : Nat) : Bool :=
  slK TQ.cnt (nqWK 12 5 TQ.cnt TQ.PL TQCl TQN) (Nat.mul 64 k) 64

@[expose] noncomputable def nqQI : Bool :=
  allN 5 (fun j => findPtK TQ.cnt TQ.T (conjQK 11200 14 (mask 14) 5 TQ.T TCG TCGI) TQN j)

@[expose] noncomputable def nqQG : Bool :=
  nqGK 11200 14 (mask 14) 6 5 TQ.cnt TQ.T TQ.GI TCG TCGI TQCl TQN

@[expose] noncomputable def c3At (i : Nat) : Bool :=
  strictB (TE.T i) (fun y => bIf(Nat.beq (pc y y) Z2K,
    strictB (pc (pc CK y) CKI) (fun x => allN TE.cnt (fun q => bIf(Nat.beq (TE.T q) x, false, true))),
    true))

@[expose] noncomputable def nePtK (c ci y t : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih p => bIf(Nat.beq (pg 14 (mask 14) t p)
      (pg 14 (mask 14) c (pg 14 (mask 14) y (pg 14 (mask 14) ci p))), ih (Nat.succ p), true))

@[expose] noncomputable def sqPre (z y : Nat) : Bool :=
  allN 8 (fun p => Nat.beq (pg 14 (mask 14) y (pg 14 (mask 14) y p)) (pg 14 (mask 14) z p))

@[expose] noncomputable def harCO0 : Nat :=
  5241692091705972577246190935080096482892823185797037161686829427073632988680849980967877962134238989107230279391209462201555326080699829179618782435196184275681670742670189991765592027342300169897876416828747565312928584239982563725969753918652890146794868762790917843667348326386982639617396094695011018478234969645531899387000242956811427516768226476126629879749760655322191034148734207081728048744998086869318257927522140937796999105262498842946598519521134370347529762351153792344883580117927656664757382294297011590950921942810594109399300752801653783943290034026151409418300683023839824045278069679983602049145200777570726429425685125293210348555572292801605464942182694261383838706326630511150752552048399717191086878229894326956640882579428987707457692007426772276594033904792978353059214962647458496012612415835875240284055997334752438663393997860597850254824955149772721833954458010054695534323384271075818998476801233658532052098456534973877021865937522376433315142323183302633591575492770073384762507897600366598273547263723873756155372063202659234546907702920417861623585444967757285950256785545398577136259024447227338797683395083616826546105093685856328003183827729526919841969132268786610077277256719534905914399467305917201422914833411979589128761240987338803046784321158930114364431478402936908831858453153769563430001042417088852789878538018863693233573963489245622128044784933887218646953648861625525505961804762496655287658037249402103559335723893426632450003244012558755753123072522982775123422387877025873713649079814979676652785940901133743097074175167032881893220793186137514250085207084018855205105468385403924799114091665512239132003110130121311074139143323647166614123007336919777334557185728109633739536829222343832288086951451675738981029519236037531025855239012177499279421862315234078128967233217698658949824248704563247268251079687966791327390168277209921820183488694871241304148376927578955745658268495723717468333927992618098618559538690486133505510395969357873823608474743156326415076325761801672005418477104083011638054131751393312789448420841057177896656514401521926951620757905685130810361167064288993214382067275364091939988750568368585084119216601364864132454693708707227019438698116989509894631612948312976536471874446053446406541689232389302555988914414320729279412009107568368585290030242725079342538244986278538296030681593887031244285289710895023702959297990815067309466761410136980788987374335253519430681000113638614782533301227148526833172740475796029992020716198700973795898459933659956017042337896644460537877084332253095092597540750097369896183347631657275758084554960360688826322639159142673583972486856632602620827027823746396336003442131336759801100957335376395789686608812141524754090952862051192991235156334741024818178479165952933296320438663610387111483872153666231276010821434765494086023246105140874292851900439895019929336062719537778391196572505318335375773883684091329997236095933554064794703071157313640914863757514405280678514659386646519235644877778997269240551871892660506458100210639022844944478652516164980372420966636134778801096293705164957942969629841052077152404639140842866750587911688767300529399909024467828887794657818778940225653285121508320794777336749797876932008826434287790389731222514992430796219069626620948381037850893492382726858721276845110566333460462974907595796777679435333649

@[expose] noncomputable def o0At (v : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight harCO0 v) 1) 1

theorem harC_o0 : allN TE.cnt (fun q => o0At (pg 14 (mask 14) (TE.T q) 0)) = true := by
  quickRfl

theorem harC_ci0 : Nat.beq (pg 14 (mask 14) CKI 0) 0 = true := by
  rw [harC_CKI]
  quickRfl

@[expose] noncomputable def harCM : Nat :=
  1189731495357231765085759326628007130763444687096510237472674821233261358180483686904488595472612039915115437484839309258897667381308687426274524698341565006080871634366004897522143251619531446845952345709482135847036647464830984784714280967845614138476044338404886122905286855313236158695999885790106357018120815363320780964323712757164290613406875202417365323950267880089067517372270610835647545755780793431622213451903817859630690311343850657539360649645193283178291767658965405285113556134369793281725888015908414675289832538063419234888599898980623114025121674472051872439321323198402942705341366951274739014593816898288994445173400364617928377138074411345791848573595077170437644191743889644885377684738322240608239079061399475675334739784016491742621485229014847672335977897158397334226349734811441653077758250988926030894789604676153104257260141806823027588003441951455327701598071281589597169413965608439504983171255062282026626200048042149808200002060993433681237623857880627479727072877482838438705048034164633337013385405998040701908662387301605018188262573723766279240798931717708807901740265407930976419648877869604017517691938687988088008944251258826969688364194133945780157844364946052713655454906327187428531895100278695119323496808703630436193927592692344820812834297364478686862064169042458555136532055050508189891866846863799917647547291371573500701015197559097453040033031520683518216494195636696077748110598284901343611469214274121810495077979275556645164983850062051066517084647369464036640569339464837172183352956873912042640003611618788934676179689647652014496253878914480937828412359726167536982001799359019885080793234034213572586043542611379125520378538226047699654432136176371325024221735487012286901531424052679816127763561575367169864748556113336628385561292447234347557621301303272811391731292205429338910813329013871747217193887297363253381309308993689163085405650637899845682143961238434098285777106879279811689613914536789986549358496033882718399609558268760019423210663931623185311122246934160633936996450671071537293409917904864258996355798770854744730994888689562105045602739741377618096935560016168197997265969761259084438033255814675757672478626032979818214948560261137198546794163864304871180914941199299504632284711683801411437700117379433218531535803392665288487266914086280705337736139519949426733809807790512433618814923376352678678741569483796764700717144016453649542530815950630088491954574919809646317616739698797002546872832124958885812704771394043721981601760934342793399553064008145621702756033687460661763750225217428893369446282133979720416234824995609204896898902536099370948162025936981570702679577360447723930576228460405307290405442002022655721628114401141715356739534147672446848218599509418924080524691521654867226008770051999465577511673942178375309390792920530271339050960211479702761414743753257909046995045237081881058749486407160845803118550385512717315946512801942511319177980503264030005696818313473936445263350259458625350468970472817780403937381183010820760342872241283506284664823102326078637668991996863838313513254604999285251086716338714085373020922264738219663556408608090959460895807485500812421860092330994464720453170356587959880695235229795500153804625265387574003714951792323290642785245417133531834827027093334822473646615830052688888165028268356334309244601808089929930973422804693617017443645540234075224375247968801049377203567198935030147857036574858303647887820340769442051122255992231825719072015904996545954331810698107750615560771092455789306642861380056901076346278384063949115826823531150398542573597477275351535710311158509036886316206057299291553022924756921969508125731167517053715581995034499333551386508822856634752777086543587845476547991299793074273996528836321424048306493072755391300381233326497479021522214117673581155221803707197628439129456700515388445731151421056171841410909929959390768984490332913500528457655715791934623572285825254482091963948083587022325277397653292568552416650016289890230681466919461788135548669365721182594983530894848308433762962475316176988702257806190740230065796316430655809668785480412920608291869536033356795330727977824249729500614736493870659946012906539441432081675153134077151975129157661566843150981175895207804379274710862278775884722966835131259242194777172586195354170887709460247193760370602495232395541564213368546974440993689108847636057772999593093318571039855634566350842723833651622095092757035575245052018547438246255703055334600359267560578343985124246178023822186086357443574828434985809104086063645889964274013818385993793843806622628838391227606806979057629271822815664977907356651912092999449096112746548220340053725721790980095323845707788202512417069891621506130600115417470678670896682560514486253226414054794384676360558805301362519925005470663568097300927397268182614590032075110557885079840194748495050901013352822507402969786676772312405435994492421707256941131585273462801

@[expose] noncomputable def m0At (v : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight harCM v) 1) 1

theorem harC_m : allN 16384 (fun p => bIf(o0At (pg 14 (mask 14) CK p), m0At p, true)) = true := by
  quickRfl

@[expose] noncomputable def c3P (c ci z i : Nat) : Bool :=
  strictB (TE.T i) (fun y => bIf(sqPre z y, bIf(m0At (pg 14 (mask 14) y 0),
    allN TE.cnt (fun q => nePtK c ci y (TE.T q) 11200 0), true), true))

theorem harC_Z2T : Z2K = pc (TE.T 1003) (TE.T 88) := by
  unfold Z2K
  rw [harC_C0T, harC_Z1T]

theorem harC_TZ2 : Nat.beq (TE.T 898) Z2K = true := by
  rw [harC_Z2T]
  quickRfl

@[expose] noncomputable def c3S (k : Nat) : Bool :=
  strictB (TE.T 898) (fun z => slK TE.cnt (c3P CK CKI z) (Nat.mul 128 k) 128)

end CFSG.KD.TwoHS

end
