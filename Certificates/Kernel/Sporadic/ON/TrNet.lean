module

public import Certificates.Kernel.Sporadic.ON.TrPt
public import Certificates.Kernel.Sporadic.ON.TrNetData
public import CFSG.Certificates.Kernel.BenesW
public import CFSG.Certificates.Kernel.BabyMonster.Native.DyLane

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.KS.FLGen CFSG.KC.BenesW

@[expose] noncomputable def spK (b : Nat) : Nat :=
  CFSG.KC.BM.rep (CFSG.KC.BM.onesN (Nat.shiftLeft (nat_lit 1) b))
    (Nat.mul (nat_lit 18) (Nat.shiftLeft (nat_lit 1) (Nat.succ b)))
    (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 17) b))

@[expose] noncomputable def spKs : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun b acc => List.cons (spK b) acc) (nat_lit 18)

@[expose] noncomputable def stg (Dt k : Nat) : Nat :=
  Nat.land (Nat.shiftRight Dt (Nat.mul (nat_lit 262144) k)) (CFSG.KC.BM.onesN (nat_lit 262144))

@[expose] noncomputable def csL (Ks : List Nat) (Dt : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun k acc => List.cons (CFSG.KC.BM.lnSpr Ks (nat_lit 2228224) (stg Dt (Nat.sub (nat_lit 34) k)))
      acc) (nat_lit 35)

@[expose] noncomputable def mapW (cl : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun c _ acc => List.cons (wid c) acc) cl

@[expose] noncomputable def revL (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun a _ ih acc => ih (List.cons a acc)) l List.nil

@[expose] noncomputable def Ds18 : List Nat :=
  [2359296, 1179648, 589824, 294912, 147456, 73728, 36864, 18432, 9216, 4608, 2304, 1152, 576,
    288, 144, 72, 36, 18, 36, 72, 144, 288, 576, 1152, 2304, 4608, 9216, 18432, 36864, 73728,
    147456, 294912, 589824, 1179648, 2359296]

@[expose] noncomputable def Rr : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 4718592)) (nat_lit 1)) (nat_lit 262143)

@[expose] noncomputable def Eid : Nat :=
  Nat.div (Nat.add (nat_lit 262144) (Nat.mul (Nat.shiftLeft (nat_lit 1) (nat_lit 4718592))
    (Nat.sub (Nat.mul (nat_lit 262143) (nat_lit 262144)) (nat_lit 262144)))) (nat_lit 68718952449)

@[expose] noncomputable def subRL (R : Nat) (cl : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(Nat.beq (Nat.land c R) c, ih)) cl

@[expose] noncomputable def validL (Ms Ds : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun M _ ih Ds => List.rec (motive := fun _ => Bool) true
      (fun D Ds' _ => bAnd(CFSG.KC.MonsterConv.Perm.dswValid (nat_lit 4718592) D M,
        bAnd(Nat.beq (Nat.mod D (nat_lit 18)) (nat_lit 0), ih Ds'))) Ds) Ms Ds

@[expose] noncomputable def chk (R a : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (Nat.mul (nat_lit 9216) a)) (CFSG.KC.BM.onesN (nat_lit 9216))

@[expose] noncomputable def leafG (X : Nat → Nat) (R N W : Nat) : Bool :=
  bAnd(allBlk (nat_lit 0) (fun a => Nat.beq (chk R a) (X a)) N,
    Nat.beq (Nat.land (Nat.shiftRight R (Nat.mul (nat_lit 9216) N)) (CFSG.KC.BM.onesN W)) (X N))

@[expose] noncomputable def leafOK (X : Nat → Nat) (R : Nat) : Bool :=
  leafG X R (nat_lit 479) (nat_lit 4896)

@[expose] noncomputable def netOK (R : Nat) (X : Nat → Nat) (cl : List Nat) : Bool :=
  forceL cl fun cl' => bAnd(subRL R cl', forceL (mapW cl') fun Ms =>
    bAnd(validL Ms Ds18, forceN (CFSG.KC.BM.benes Ms Ds18 Eid) fun E => leafOK X E))

@[expose] noncomputable def DtOf (h : Nat) : Nat :=
  nIf(Nat.beq h 0, ONN.M0, nIf(Nat.beq h 1, ONN.M1, nIf(Nat.beq h 2, ONN.M2,
    nIf(Nat.beq h 3, ONN.M3, nIf(Nat.beq h 4, ONN.M4, nIf(Nat.beq h 5, ONN.M5, ONN.M6))))))

@[expose] noncomputable def XF (c : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat)
    ((fun h => Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat)
      (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat)
        (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) ONB.U6
          ONB.U5 (Nat.beq h 5)) ONB.U4 (Nat.beq h 4)) ONB.U3 (Nat.beq h 3)) ONB.U2 (Nat.beq h 2))
        ONB.U1 (Nat.beq h 1)) ONB.U0 (Nat.beq h 0)) (Nat.shiftRight c 1))
    ((fun h => Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat)
      (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat)
        (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) ONB.T6
          ONB.T5 (Nat.beq h 5)) ONB.T4 (Nat.beq h 4)) ONB.T3 (Nat.beq h 3)) ONB.T2 (Nat.beq h 2))
        ONB.B (Nat.beq h 1)) ONB.A (Nat.beq h 0)) (Nat.shiftRight c 1))
    (Nat.beq (Nat.land c 1) 0)

@[expose] noncomputable def clOf (Ks : List Nat) (c : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (revL (csL Ks (DtOf (Nat.shiftRight c 1))))
    (csL Ks (DtOf (Nat.shiftRight c 1))) (Nat.beq (Nat.land c 1) 0)

@[expose] noncomputable def netC (c : Nat) : Bool :=
  forceL spKs fun Ks => forceN Rr fun R => netOK R (XF c) (clOf Ks c)

@[expose] noncomputable def selN (n0 n1 n2 n3 n4 n5 n6 : List Nat) (c : Nat) : List Nat :=
  (fun l => Bool.rec (motive := fun _ => List Nat) (revL l) l (Nat.beq (Nat.land c 1) 0))
    ((fun h => Bool.rec (motive := fun _ => List Nat) (Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) (Bool.rec (motive := fun _ => List Nat)
        (Bool.rec (motive := fun _ => List Nat) (Bool.rec (motive := fun _ => List Nat) n6
          n5 (Nat.beq h 5)) n4 (Nat.beq h 4)) n3 (Nat.beq h 3)) n2 (Nat.beq h 2))
        n1 (Nat.beq h 1)) n0 (Nat.beq h 0)) (Nat.shiftRight c 1))

@[expose] noncomputable def wordC (j : Nat) : Bool :=
  forceL spKs fun Ks => forceL (mapW (csL Ks ONN.M0)) fun n0 => forceL (mapW (csL Ks ONN.M1))
    fun n1 => forceL (mapW (csL Ks ONN.M2)) fun n2 => forceL (mapW (csL Ks ONN.M3)) fun n3 =>
      forceL (mapW (csL Ks ONN.M4)) fun n4 => forceL (mapW (csL Ks ONN.M5)) fun n5 =>
        forceL (mapW (csL Ks ONN.M6)) fun n6 =>
          forceN (wordG (selN n0 n1 n2 n3 n4 n5 n6) Ds18 (ONV.WC j) (ONV.WL j) Eid) fun E =>
            leafOK (XF (Nat.mul 2 j)) E

@[expose] noncomputable def wordK (k : Nat) : Bool := wordC (Nat.add (nat_lit 2) k)

@[expose] noncomputable def eidA (ch a : Nat) : Bool :=
  allBlk (nat_lit 0) (fun b =>
    Nat.beq (Nat.land (Nat.shiftRight ch (Nat.mul (nat_lit 18) b)) (nat_lit 262143))
      (Nat.add (Nat.mul (nat_lit 512) a) b)) (nat_lit 512)

@[expose] noncomputable def eidOK : Bool :=
  forceN Eid fun E => allBlk (nat_lit 0) (fun a => forceN (chk E a) fun ch => eidA ch a) (nat_lit 512)

@[expose] noncomputable def eidS (_ : Nat) : Bool := eidOK

theorem band_tt {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem onesN_eq (k : Nat) : CFSG.KC.BM.onesN k = 2 ^ k - 1 := by
  change 1 <<< k - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem land_ones (x k : Nat) : Nat.land x (2 ^ k - 1) = x % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod x k

theorem shr_eq (x k : Nat) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k

theorem fld18_eq (x f : Nat) :
    Nat.land (Nat.shiftRight x (Nat.mul 18 f)) 262143 = fw 18 x f := by
  rw [show (262143 : Nat) = 2 ^ 18 - 1 from rfl, land_ones, shr_eq]
  rfl

theorem chk_gen (R a w : Nat) :
    Nat.land (Nat.shiftRight R (Nat.mul w a)) (CFSG.KC.BM.onesN w) = R / 2 ^ (w * a) % 2 ^ w := by
  rw [onesN_eq, land_ones, shr_eq]
  rfl

theorem chk_eq (R a : Nat) : chk R a = R / 2 ^ (9216 * a) % 2 ^ 9216 := chk_gen R a 9216

theorem fw_chunk (x a b w : Nat) (hb : 18 * b + 18 ≤ w) :
    fw 18 x (512 * a + b) = fw 18 (x / 2 ^ (9216 * a) % 2 ^ w) b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fw, testBit_fw, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 18
  · have h1 : 18 * b + i < w := by omega
    have h2 : 18 * (512 * a + b) + i = 18 * b + i + 9216 * a := by omega
    simp [hi, h1, h2]
  · simp [hi]

theorem tb_eq (X : Nat → Nat) (f : Nat) : tb X f = fw 18 (X (f / 512)) (f % 512) := by
  unfold tb rget
  rw [CFSG.KS.TW.strictN_eq']
  change Nat.land (Nat.shiftRight (X (Nat.shiftRight f 9)) (Nat.mul 18 (Nat.land f 511)))
    (Nat.sub (Nat.shiftLeft 1 18) 1) = _
  rw [show Nat.sub (Nat.shiftLeft 1 18) 1 = 262143 from rfl, fld18_eq, shr_eq,
    show (511 : Nat) = 2 ^ 9 - 1 from rfl, land_ones]

theorem leaf_gen {X : Nat → Nat} {R N W : Nat} (h : leafG X R N W = true) :
    ∀ f, f / 512 < N ∨ (f / 512 = N ∧ 18 * (f % 512) + 18 ≤ W) → fw 18 R f = tb X f := by
  intro f hf
  obtain ⟨h1, h2⟩ := band_tt h
  rw [tb_eq, show fw 18 R f = fw 18 R (512 * (f / 512) + f % 512) by rw [Nat.div_add_mod]]
  rcases hf with ha | ⟨ha, hw⟩
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec h1 (f / 512) ha)
    rw [Nat.add_eq, Nat.zero_add] at e
    rw [← e, chk_eq]
    exact fw_chunk R (f / 512) (f % 512) 9216 (by omega)
  · have e := Nat.eq_of_beq_eq_true h2
    rw [ha, ← e, onesN_eq, land_ones, shr_eq]
    exact fw_chunk R N (f % 512) W hw

theorem leaf_rng (f : Nat) (hf : f < 245520) :
    f / 512 < 479 ∨ (f / 512 = 479 ∧ 18 * (f % 512) + 18 ≤ 4896) := by
  omega

theorem leafOK_spec {X : Nat → Nat} {R : Nat} (h : leafOK X R = true) :
    ∀ f < 245520, fw 18 R f = tb X f := by
  intro f hf
  exact leaf_gen (N := 479) (W := 4896) h f (leaf_rng f hf)

theorem eid_fw (hE : eidOK = true) : ∀ f < 262144, fw 18 Eid f = f := by
  intro f hf
  unfold eidOK at hE
  simp only [forceN_eq] at hE
  have h1 := allBlk_spec hE (f / 512) (by omega)
  simp only [Nat.add_eq, Nat.zero_add, forceN_eq] at h1
  have h2 := allBlk_spec h1 (f % 512) (Nat.mod_lt _ (by decide))
  simp only [Nat.add_eq, Nat.zero_add] at h2
  rw [fld18_eq, chk_eq] at h2
  have e := Nat.eq_of_beq_eq_true h2
  rw [← fw_chunk Eid (f / 512) (f % 512) 9216 (by omega)] at e
  rw [← Nat.div_add_mod f 512]
  exact e

theorem rr_gen (S : Nat) : Nat.div (Nat.sub (Nat.shiftLeft 1 S) 1) 262143 =
    1 * ((2 ^ S - 1) / (2 ^ 18 - 1)) := by
  rw [Nat.one_mul]
  change (1 <<< S - 1) / 262143 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_Rr (q : Nat) : Rr.testBit q = true → q % 18 = 0 := by
  intro h
  have e : Rr = 1 * ((2 ^ 4718592 - 1) / (2 ^ 18 - 1)) := rr_gen 4718592
  rw [e, CFSG.KC.Benes.testBit_mul_div (W := 4718592) (L := 18) (n := 262144) (c := 1)
    (by decide) rfl (by decide)] at h
  obtain ⟨-, h⟩ := Bool.and_eq_true_iff.1 h
  revert h
  cases q % 18 with
  | zero => intro _; rfl
  | succ k =>
    intro h
    rw [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (Nat.succ_ne_zero k))] at h
    exact absurd h Bool.false_ne_true

theorem netV_of : ∀ (cl Ds : List Nat), subRL Rr cl = true → validL (mapW cl) Ds = true →
    NetV 18 4718592 (mapW cl) Ds
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | c :: cl, D :: Ds, hs, hv => by
    obtain ⟨hc, hs'⟩ := band_tt hs
    obtain ⟨hd, hr⟩ := band_tt hv
    obtain ⟨hm, hv'⟩ := band_tt hr
    have hc' := Nat.eq_of_beq_eq_true hc
    change Aligned 18 (wid c) ∧ (∃ d, D = 18 * d) ∧ CFSG.KC.Benes.ValidIn 4718592 D (wid c) ∧
      NetV 18 4718592 (mapW cl) Ds
    refine ⟨aligned_wid fun q hq => testBit_Rr q ?_, ⟨D / 18, ?_⟩, ?_, netV_of cl Ds hs' hv'⟩
    · rw [← hc'] at hq
      change (c &&& Rr).testBit q = true at hq
      rw [Nat.testBit_and] at hq
      exact (Bool.and_eq_true_iff.1 hq).2
    · have := Nat.eq_of_beq_eq_true hm
      change D % 18 = 0 at this
      omega
    · change Bool.rec (motive := fun _ => Bool) false _ _ = true at hd
      obtain ⟨d1, d2⟩ := band_tt hd
      exact CFSG.KC.Benes.validIn_of_dsw (Nat.eq_of_beq_eq_true d1) (Nat.eq_of_beq_eq_true d2)

theorem netOK_sound (hE : eidOK = true) {X : Nat → Nat} {cl : List Nat}
    (h : netOK Rr X cl = true) :
    ∀ x, ∀ f < 245520, fw 18 (CFSG.KC.BM.benes (mapW cl) Ds18 x) f = fw 18 x (tb X f) := by
  unfold netOK at h
  simp only [forceL_eq, forceN_eq] at h
  obtain ⟨hs, hr⟩ := band_tt h
  obtain ⟨hv, hl⟩ := band_tt hr
  obtain ⟨P, hP, hlt, -⟩ := benes_fw (W := 18) (S := 4718592) (n := 262144) (by decide) rfl
    (mapW cl) Ds18 (netV_of cl Ds18 hs hv)
  intro x f hf
  have e := leafOK_spec hl f hf
  rw [hP, eid_fw hE _ (hlt f (by omega))] at e
  rw [hP, e]

theorem net_fact (hE : eidOK = true) (hN : ∀ c < 16, netC c = true) :
    ∀ c < 16, ∀ x, ∀ f < 245520,
      fw 18 (CFSG.KC.BM.benes (mapW (clOf spKs c)) Ds18 x) f = fw 18 x (tb (XF c) f) := by
  intro c hc
  have h := hN c hc
  unfold netC at h
  simp only [forceL_eq, forceN_eq] at h
  exact netOK_sound hE h

theorem revL_eq (l : List Nat) : revL l = l.reverse := by
  have : ∀ (l acc : List Nat), List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun a _ ih acc => ih (List.cons a acc)) l acc = l.reverse ++ acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons a l ih => intro acc; rw [List.reverse_cons, List.append_assoc]; exact ih (a :: acc)
  rw [revL, this, List.append_nil]

theorem mapW_eq (l : List Nat) : mapW l = l.map wid := by
  induction l with
  | nil => rfl
  | cons a l ih => change wid a :: mapW l = _; rw [ih, List.map_cons]

theorem selN_eq (c : Nat) : selN (mapW (csL spKs ONN.M0)) (mapW (csL spKs ONN.M1))
    (mapW (csL spKs ONN.M2)) (mapW (csL spKs ONN.M3)) (mapW (csL spKs ONN.M4))
    (mapW (csL spKs ONN.M5)) (mapW (csL spKs ONN.M6)) c = mapW (clOf spKs c) := by
  unfold selN clOf DtOf
  dsimp only
  cases Nat.beq (Nat.land c 1) 0 <;> cases Nat.beq (Nat.shiftRight c 1) 0 <;>
    cases Nat.beq (Nat.shiftRight c 1) 1 <;> cases Nat.beq (Nat.shiftRight c 1) 2 <;>
    cases Nat.beq (Nat.shiftRight c 1) 3 <;> cases Nat.beq (Nat.shiftRight c 1) 4 <;>
    cases Nat.beq (Nat.shiftRight c 1) 5 <;>
    simp only [revL_eq, mapW_eq, List.map_reverse]

@[expose] noncomputable def GL (c v : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c 1) 0, TB (Nat.shiftRight c 1) v, UB (Nat.shiftRight c 1) v)

theorem GL_eq (c v : Nat) : GL c v = tb (XF c) v := by
  unfold GL XF TB UB
  dsimp only
  cases Nat.beq (Nat.land c 1) 0 <;> cases Nat.beq (Nat.shiftRight c 1) 0 <;>
    cases Nat.beq (Nat.shiftRight c 1) 1 <;> cases Nat.beq (Nat.shiftRight c 1) 2 <;>
    cases Nat.beq (Nat.shiftRight c 1) 3 <;> cases Nat.beq (Nat.shiftRight c 1) 4 <;>
    cases Nat.beq (Nat.shiftRight c 1) 5 <;> rfl

theorem trace_gen' (TT UU : Nat → Nat → Nat) (W : Nat) : ∀ (L k v : Nat),
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
      (fun _ ih k v => strictN (fld(W, Nat.mul (nat_lit 4) k, nat_lit 15)) fun c =>
        strictN (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), TT (Nat.shiftRight c (nat_lit 1)) v,
          UU (Nat.shiftRight c (nat_lit 1)) v)) fun v' => ih (Nat.succ k) v') L k v =
    traceG (fun c v => nIf(Nat.beq (Nat.land c 1) 0, TT (Nat.shiftRight c 1) v,
      UU (Nat.shiftRight c 1) v)) W L k v
  | 0, k, v => rfl
  | L + 1, k, v => by
    simp only []
    rw [CFSG.KS.TW.strictN_eq', CFSG.KS.TW.strictN_eq', trace_gen' TT UU W L (k + 1), traceG]
    rfl

theorem traceG_congr {G1 G2 : Nat → Nat → Nat} {m : Nat}
    (h : ∀ c, ∀ f < m, G1 c f = G2 c f ∧ G2 c f < m) (Wd : Nat) :
    ∀ L k v, v < m → traceG G1 Wd L k v = traceG G2 Wd L k v
  | 0, _, _, _ => rfl
  | L + 1, k, v, hv => by
    rw [traceG, traceG, (h _ v hv).1]
    exact traceG_congr h Wd L (k + 1) _ (h _ v hv).2

section

variable (hx : ∀ x < 245520, trAtP x = true)

include hx in
theorem agreeP_lt : ∀ h < 7, ∀ v < 245520, TB h v = TT h v ∧ UB h v = UU h v ∧
    TT h v < 245520 ∧ UU h v < 245520 := by
  intro h hh v hv
  have e := hx v hv
  unfold trAtP at e
  obtain ⟨hp, ha⟩ := bAnd_iff.1 e
  have h1 := allBlk_spec hp h hh
  have h2 := allBlk_spec ha h hh
  rw [Nat.add_eq, Nat.zero_add] at h1 h2
  rw [strictB_eq] at h1
  obtain ⟨a1, h4⟩ := bAnd_iff.1 h1
  obtain ⟨a2, -⟩ := bAnd_iff.1 h4
  obtain ⟨b1, b2⟩ := bAnd_iff.1 h2
  exact ⟨Nat.eq_of_beq_eq_true b1, Nat.eq_of_beq_eq_true b2, Nat.blt_eq.mp a1, Nat.blt_eq.mp a2⟩

include hx in
theorem agreeP_all : ∀ h, ∀ v < 245520, TB h v = TT h v ∧ UB h v = UU h v ∧
    TT h v < 245520 ∧ UU h v < 245520 := by
  intro h v hv
  rcases Nat.lt_or_ge h 7 with hh | hh
  · exact agreeP_lt hx h hh v hv
  · obtain ⟨k, rfl⟩ : ∃ k, h = k + 7 := ⟨h - 7, by omega⟩
    exact agreeP_lt hx 6 (by omega) v hv

include hx in
theorem GL_agree : ∀ c, ∀ f < 245520, GL c f =
    nIf(Nat.beq (Nat.land c 1) 0, TT (Nat.shiftRight c 1) f, UU (Nat.shiftRight c 1) f) ∧
    nIf(Nat.beq (Nat.land c 1) 0, TT (Nat.shiftRight c 1) f, UU (Nat.shiftRight c 1) f) < 245520 := by
  intro c f hf
  obtain ⟨a1, a2, a3, a4⟩ := agreeP_all hx (Nat.shiftRight c 1) f hf
  unfold GL
  cases Nat.beq (Nat.land c 1) 0
  · exact ⟨a2, a4⟩
  · exact ⟨a1, a3⟩

include hx in
theorem wordC_sound (hE : eidOK = true) (hN : ∀ c < 16, netC c = true) {j : Nat}
    (hj : 2 ≤ j) (hj7 : j < 7) (hw : wordC j = true) :
    ∀ v < 245520, TT j v = trace TT UU (ONV.WC j) (ONV.WL j) v := by
  intro v hv
  unfold wordC at hw
  simp only [forceL_eq, forceN_eq] at hw
  have hs : selN (mapW (csL spKs ONN.M0)) (mapW (csL spKs ONN.M1))
      (mapW (csL spKs ONN.M2)) (mapW (csL spKs ONN.M3)) (mapW (csL spKs ONN.M4))
      (mapW (csL spKs ONN.M5)) (mapW (csL spKs ONN.M6)) = fun c => mapW (clOf spKs c) :=
    funext selN_eq
  rw [hs] at hw
  have hG : ∀ c < 16, ∀ x, ∀ f < 245520, fw 18 (CFSG.KC.BM.benes (mapW (clOf spKs c)) Ds18 x) f =
      fw 18 x (GL c f) := fun c hc x f hf => by rw [GL_eq]; exact net_fact hE hN c hc x f hf
  have hm : ∀ c < 16, ∀ f < 245520, GL c f < 245520 := fun c _ f hf => by
    rw [(GL_agree hx c f hf).1]
    exact (GL_agree hx c f hf).2
  obtain ⟨e1, e2⟩ := wordG_fw hG hm (ONV.WC j) (ONV.WL j) Eid v hv
  have e3 := leafOK_spec hw v hv
  rw [e1, eid_fw hE _ (by omega), ← GL_eq] at e3
  have eT : GL (Nat.mul 2 j) v = TT j v := by
    rw [← (agreeP_lt hx j hj7 v hv).1]
    obtain rfl | rfl | rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    all_goals rfl
  unfold trace
  rw [trace_gen', ← traceG_congr (GL_agree hx) _ _ _ _ hv, e3, eT]

end

theorem trS_of_net (hP : ∀ s < 1023, trP s = true) (hE : eidOK = true)
    (hN : ∀ c < 16, netC c = true) (hW : ∀ k < 5, wordK k = true) :
    ∀ s < 1023, trS s = true := by
  have hx : ∀ x < 245520, trAtP x = true := by
    intro x hx
    have := allBlk_spec (hP (x / 240) (by omega)) (x % 240) (Nat.mod_lt _ (by omega))
    have e : Nat.add (Nat.mul (x / 240) 240) (x % 240) = x := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rwa [e] at this
  intro s hs
  unfold trS trRange
  refine allBlk_of fun l hl => ?_
  have hl' : l < 240 := hl
  have hxl : Nat.add (Nat.mul s 240) l < 245520 := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  have e := hx _ hxl
  unfold trAtP at e
  obtain ⟨hp, -⟩ := bAnd_iff.1 e
  unfold trAt
  refine bAnd_iff.2 ⟨hp, allBlk_of fun k hk => ?_⟩
  have hk' : k < 5 := hk
  rw [wordC_sound hx hE hN (j := Nat.add 2 k) (by change 2 ≤ 2 + k; omega)
    (by change 2 + k < 7; omega) (hW k hk') _ hxl]
  exact Nat.beq_refl _

end CertificateChecks.KernelSpor.ON

end
