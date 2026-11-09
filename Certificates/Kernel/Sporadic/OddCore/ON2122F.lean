module

public import Certificates.Kernel.Sporadic.OddCore.ON2122M
public import Certificates.Kernel.Sporadic.OddCore.ON2122P0
public import Certificates.Kernel.Sporadic.OddCore.ON2122P3
public import Certificates.Kernel.Sporadic.OddCore.ON2122P9
public import Certificates.Kernel.Sporadic.OddCore.ON2122P10
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import Certificates.Kernel.Sporadic.OddCore.ON2121
public import Certificates.Kernel.Sporadic.OddCore.ON2123
public import Certificates.Kernel.Sporadic.ON3.Elements
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.DecSLSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Sporadic.ONOddCore.GraphEnum
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Certificates.Kernel.Kc3E16TSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.LiftResT CFSG.Sporadic.ONOddCore.liftResText

namespace CertificateChecks.KernelSpor.ON2122

open CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.DecSL
open CFSG.KC.BfsPin
open CFSG.KC.Enum hiding pcomp
open CFSG.Monster.B.Co2.Native (compA idA)
open CFSG.ONSchreier.Native (peq)

theorem digits : digitsSLOK LiftResT.chars = true := by
  quickRfl

theorem nats_eq : liftResNats = natsSL LiftResT.chars := by
  rw [liftResNats, LiftResT.eq, natsOf_ofList digits]

@[expose] noncomputable def YK : Array Nat := ((natsSL LiftResT.chars).take 480).toArray

@[expose] noncomputable def RL (j : Nat) : List Nat :=
  ((natsSL LiftResT.chars).drop (480 * (j + 1))).take 480

@[expose] noncomputable def RK (j : Nat) : Array Nat := (RL j).toArray

theorem resY_eq : resY = YK := by
  rw [resY, nats_eq]
  rfl

theorem resArrs_get_eq {j : Nat} (hj : j < 3) : resArrs[j]! = RK j := by
  have e : resArrs[j]! = resArr j := by interval_cases j <;> rfl
  rw [e, resArr, nats_eq]
  rfl

@[expose] noncomputable def posK (n w k : Nat) (G : Nat → Nat) (wd : List Nat) : Nat :=
  wd.foldr (fun l acc => CFSG.KC.Enum.pcomp n w (mask w)
    (if l - 1 < k then G (l - 1) else pidn n w) acc) (pidn n w)

theorem getD_eq {gs : Array (Array Nat)} {i : Nat} {d : Array Nat} :
    gs.getD i d = if i < gs.size then gs[i]! else d := by
  by_cases h : i < gs.size
  · simp only [h, ↓reduceIte]
    rw [getElem!_pos gs i h]
    simp [Array.getD, h]
  · simp [Array.getD, h]

theorem posArr_unpack {n w k : Nat} {G : Nat → Nat} {gs : Array (Array Nat)}
    (hid : idK n w (mask w) = true) (hcI : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hs : gs.size = k)
    (hg : ∀ j < k, gs[j]! = unpack n w (G j) ∧ canonK n w (mask w) (n * w) (G j) = true) :
    ∀ wd : List Nat, posArr n gs wd = unpack n w (posK n w k G wd) ∧
      canonK n w (mask w) (n * w) (posK n w k G wd) = true := by
  intro wd
  induction wd with
  | nil =>
    refine ⟨?_, hcI⟩
    change idA n = unpack n w (pidn n w)
    rw [idK_sound hid]
  | cons l wd ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hl : gs.getD (l - 1) (CFSG.ONSchreier.Native.pid n) =
        unpack n w (if l - 1 < k then G (l - 1) else pidn n w) ∧
        canonK n w (mask w) (n * w) (if l - 1 < k then G (l - 1) else pidn n w) = true := by
      rw [getD_eq, hs]
      by_cases h : l - 1 < k
      · simp only [h, ↓reduceIte]
        exact hg _ h
      · simp only [h, ↓reduceIte]
        refine ⟨?_, hcI⟩
        change idA n = unpack n w (pidn n w)
        rw [idK_sound hid]
    have e1 : posArr n gs (l :: wd) =
        CFSG.ONSchreier.Native.pcomp n (gs.getD (l - 1) (CFSG.ONSchreier.Native.pid n))
          (posArr n gs wd) := rfl
    have e2 : posK n w k G (l :: wd) = CFSG.KC.Enum.pcomp n w (mask w)
        (if l - 1 < k then G (l - 1) else pidn n w) (posK n w k G wd) := rfl
    rw [e1, e2, hl.1, ih1]
    exact ⟨compA_unpack hl.2 ih2, canonK_pcomp hl.2 ih2⟩

@[expose] noncomputable def bindL (j : Nat) : Bool :=
  bAnd(Nat.beq (RL j).length 480, bAnd((RL j).all (fun y => Nat.blt y 512),
    Nat.beq (CFSG.KC.Kc3K.packL 9 (RL j)) (PM2122.S j)))

theorem bindM : allN 3 bindL = true := by
  quickRfl

theorem toArray_unpack {l : List Nat} {P : Nat} (h : bAnd(Nat.beq l.length 480,
    bAnd(l.all (fun y => Nat.blt y 512), Nat.beq (CFSG.KC.Kc3K.packL 9 l) P)) = true) :
    l.toArray = unpack 480 9 P := by
  simp only [bAnd_iff, List.all_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlen : l.length = 480 := Nat.eq_of_beq_eq_true h1
  have hlt : ∀ y ∈ l, y < 2 ^ 9 := fun y hy =>
    lt_of_lt_of_eq (Nat.blt_eq.mp (h2 y hy)) (by norm_num)
  apply unpack_eq_of_bindArrK
  unfold bindArrK
  rw [bAnd_iff]
  refine ⟨by rw [List.size_toArray, hlen]; rfl, ?_⟩
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro i hi
  have hil : i < l.length := by rw [hlen]; exact hi
  rw [getElem!_pos l.toArray i (by simpa using hil), List.getElem_toArray,
    ← List.getD_eq_getElem _ 0 hil, ← Nat.eq_of_beq_eq_true h3,
    CFSG.KC.Kc3K.pg_packL (w := 9) (m := mask 9) (by decide) l hlt i hil]
  exact Nat.beq_refl _

theorem RK_unpack {j : Nat} (h : bindL j = true) : RK j = unpack 480 9 (PM2122.S j) := by
  rw [bindL.eq_1] at h
  rw [RK.eq_1]
  exact toArray_unpack h

theorem canonM : allN 3 (fun j => canonK 480 9 (mask 9) (480 * 9) (PM2122.S j)) = true := by
  quickRfl

theorem idK9 : idK 480 9 (mask 9) = true := by
  quickRfl

theorem canonI9 : canonK 480 9 (mask 9) (480 * 9) (pidn 480 9) = true := by
  quickRfl

theorem resArrs_bind : resArrs.size = 3 ∧ ∀ j < 3, resArrs[j]! = unpack 480 9 (PM2122.S j) :=
  ⟨rfl, fun j hj => by rw [resArrs_get_eq hj]; exact RK_unpack (allN_spec bindM j hj)⟩

theorem posArr_res (wd : List Nat) : posArr 480 resArrs wd = unpack 480 9 (posK 480 9 3 PM2122.S wd) ∧
    canonK 480 9 (mask 9) (480 * 9) (posK 480 9 3 PM2122.S wd) = true :=
  posArr_unpack idK9 canonI9 rfl (fun j hj => ⟨resArrs_bind.2 j hj, allN_spec canonM j hj⟩) wd

theorem base_of {BP : Nat} (h : allN 3 (fun t => Nat.beq (pg 9 (mask 9) BP t) t) = true) :
    (resBase.map Fin.val).toArray.size = 3 ∧
      ∀ t < 3, (resBase.map Fin.val).toArray[t]! = pg 9 (mask 9) BP t := by
  refine ⟨rfl, fun t ht => ?_⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec h t ht)]
  interval_cases t <;> rfl

theorem base2_of {BP : Nat} (h : allN 3 (fun t => Nat.beq (pg 10 (mask 10) BP t) t) = true) :
    (resBase2.map Fin.val).toArray.size = 3 ∧
      ∀ t < 3, (resBase2.map Fin.val).toArray[t]! = pg 10 (mask 10) BP t := by
  refine ⟨rfl, fun t ht => ?_⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec h t ht)]
  interval_cases t <;> rfl

theorem w0 : ∀ j < 3, resW[j]! = [] := by
  intro j hj
  interval_cases j <;> rfl

theorem wD : resW.extract 3 resW.size = resD.toArray := by
  decide

theorem chainM : CFSG.Sporadic.HNOddCore.chainCheck 480 resArrs resW resBase resSizes = true :=
  chainCheck_of resArrs_bind rfl w0 wD (by norm_num) (base_of (by quickRfl)) PM2122.head
    PM2122.hl (by norm_num) PM2122.hs (by quickRfl) (by decide +kernel)

@[expose] noncomputable def YL : List Nat := (natsSL LiftResT.chars).take 480

@[expose] noncomputable def YP : Nat := CFSG.KC.Kc3K.packL 18 YL

@[expose] noncomputable def ascB : List Nat → Bool
  | x :: y :: l => bAnd(Nat.blt x y, ascB (y :: l))
  | _ => true

@[expose] noncomputable def resK2 : Bool :=
  bAnd(Nat.beq YL.length 480, bAnd(ascB YL, bAnd(YL.all (fun y => Nat.blt y 245520),
    allN 3 (fun j => allN 480 (fun k => bAnd(Nat.blt (pg 9 (mask 9) (PM2122.S j) k) 480,
      Nat.beq (pg 18 (mask 18) YP (pg 9 (mask 9) (PM2122.S j) k))
        (ON3.mG j (pg 18 (mask 18) YP k))))))))

theorem resK2_ok : resK2 = true := by
  quickRfl

theorem ascB_spec : ∀ (l : List Nat), ascB l = true →
    ∀ k, k + 1 < l.length → l.getD k 0 < l.getD (k + 1) 0
  | [], _, k, hk => absurd hk (by simp)
  | [_], _, k, hk => absurd hk (by simp)
  | x :: y :: l, h, k, hk => by
    have h' : Nat.blt x y = true ∧ ascB (y :: l) = true := by
      simpa only [ascB, bAnd_iff] using h
    cases k with
    | zero => simpa using Nat.blt_eq.mp h'.1
    | succ k =>
      have := ascB_spec (y :: l) h'.2 k (by simp only [List.length_cons] at hk ⊢; omega)
      simpa using this

theorem getD_eq_getK (l : List Nat) {k : Nat} (hk : k < l.length) : l.getD k 0 = l[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem YK_get {k : Nat} (hk : k < YL.length) : YK[k]! = YL.getD k 0 := by
  have e : YK = YL.toArray := rfl
  rw [e, getElem!_pos YL.toArray k (by simpa using hk), List.getElem_toArray, getD_eq_getK YL hk]

theorem YP_get (hlen : YL.length = 480) (hlt : ∀ y ∈ YL, y < 245520) {k : Nat} (hk : k < 480) :
    pg 18 (mask 18) YP k = YL.getD k 0 :=
  CFSG.KC.Kc3K.pg_packL (w := 18) (m := mask 18) (by decide) YL
    (fun x hx => lt_trans (hlt x hx) (by norm_num)) k (hlen ▸ hk)

theorem RK_get {j k : Nat} (hj : j < 3) (hk : k < 480) :
    (RK j)[k]! = pg 9 (mask 9) (PM2122.S j) k := by
  rw [← resArrs_get_eq hj, resArrs_bind.2 j hj, Orb.unpack_get hk]

theorem RK_size {j : Nat} (hj : j < 3) : (RK j).size = 480 := by
  rw [← resArrs_get_eq hj, resArrs_bind.2 j hj, unpack, Array.size_ofFn]

theorem res_ok : liftResOK (wordArrs Data.MWords) = true := by
  have h := resK2_ok
  unfold resK2 at h
  simp only [bAnd_iff, List.all_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlen : YL.length = 480 := Nat.eq_of_beq_eq_true h1
  have hlt : ∀ y ∈ YL, y < 245520 := fun y hy => Nat.blt_eq.mp (h3 y hy)
  have hY : ∀ k < 480, resY[k]! = YL.getD k 0 := fun k hk => by
    rw [resY_eq, YK_get (by rw [hlen]; exact hk)]
  have hYl : ∀ k < 480, YL.getD k 0 < 245520 := fun k hk => by
    rw [getD_eq_getK YL (by omega)]
    exact hlt _ (List.getElem_mem _)
  unfold liftResOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, chainM⟩
  · have e : YK = YL.toArray := rfl
    rw [resY_eq, e, List.size_toArray, hlen]
  · rw [allBelowN_iff]
    intro k hk
    rw [hY k (by omega), hY (k + 1) (by omega)]
    simpa using ascB_spec YL h2 k (by omega)
  · rw [hY 479 (by norm_num)]
    exact hYl 479 (by norm_num)
  · rw [allBelowN_iff]
    intro j hj
    simp only [Bool.and_eq_true, beq_iff_eq, resArrs_get_eq hj]
    refine ⟨RK_size hj, ?_⟩
    rw [allBelowN_iff]
    intro k hk
    have g := allN_spec (allN_spec h4 j hj) k hk
    rw [bAnd_iff] at g
    have g1 := Nat.blt_eq.mp g.1
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rw [RK_get hj hk]
    refine ⟨g1, ?_⟩
    rw [hY _ g1, hY k hk, ← YP_get hlen hlt g1, ← YP_get hlen hlt hk, Nat.eq_of_beq_eq_true g.2,
      (ON3.m_get hj _ (by rw [YP_get hlen hlt hk]; exact hYl k hk)).1]

theorem localCert_eq : localCert = decodeCert (natsSL LocAutT.chars) := by
  rw [localCert, LocAutT.eq, natsOf_ofList ON2123.digits]

theorem liftData_eq : liftData = decodeLifts (natsSL LiftsT.chars) := by
  rw [liftData, LiftsT.eq, natsOf_ofList ON2121.digits]

@[expose] noncomputable def liftK (k i : Nat) : LiftEntry :=
  ((decodeCert (natsSL LocAutT.chars)).records.getD k default).lifts.getD i default

theorem liftAt_eq (k i : Nat) : liftAt k i = liftK k i := by
  rw [liftAt, liftK, localCert_eq]

@[expose] noncomputable def imgK (e : LiftEntry) (j : Nat) : Nat :=
  posK 480 9 3 PM2122.S (e.words.getD j [])

@[expose] noncomputable def qW : List Nat := [3, 3, 3, 3, 2, 3, 2, 2, 2, 2, 3, 2]

theorem qW_eq : (decodeLifts (natsSL LiftsT.chars)).qWord = qW := by
  decide +kernel

@[expose] noncomputable def qK : Nat := posK 480 9 3 PM2122.S qW

@[expose] noncomputable def qPowK (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 480 9) (fun _ acc => CFSG.KC.Enum.pcomp 480 9 (mask 9) qK acc) p

@[expose] noncomputable def pairK (A B P : Nat) : Bool :=
  bAnd(allN 480 (fun i => Nat.beq (pg 10 (mask 10) P i) (pg 9 (mask 9) A i)),
    allN 480 (fun i => Nat.beq (pg 10 (mask 10) P (Nat.add 480 i)) (Nat.add 480 (pg 9 (mask 9) B i))))

@[expose] noncomputable def graphK (e : LiftEntry) (P : Nat → Nat) : Bool :=
  bAnd(Nat.beq e.words.length 3, bAnd(allN 3 (fun j => pairK (PM2122.S j) (imgK e j) (P j)),
    Nat.beq (posK 480 9 3 (imgK e) qW) (qPowK e.power)))

theorem dbl_unpack_of {n w w2 A B P : Nat}
    (h1 : ∀ i < n, pg w2 (mask w2) P i = pg w (mask w) A i)
    (h2 : ∀ i < n, pg w2 (mask w2) P (n + i) = n + pg w (mask w) B i) :
    dbl n (unpack n w A) (unpack n w B) = unpack (n + n) w2 P := by
  have hsA : (unpack n w A).size = n := by rw [unpack, Array.size_ofFn]
  have hsB : (unpack n w B).size = n := by rw [unpack, Array.size_ofFn]
  have hsP : (unpack (n + n) w2 P).size = n + n := by rw [unpack, Array.size_ofFn]
  have hsD : (dbl n (unpack n w A) (unpack n w B)).size = n + n := by
    rw [dbl, Array.size_append, Array.size_map, hsA, hsB]
  apply Array.ext (hsD.trans hsP.symm)
  intro i hi1 hi2
  have hi : i < n + n := hsP ▸ hi2
  rw [← getElem!_pos (dbl n (unpack n w A) (unpack n w B)) i hi1,
    ← getElem!_pos (unpack (n + n) w2 P) i hi2, Orb.unpack_get hi]
  rcases Nat.lt_or_ge i n with hlt | hge
  · rw [dbl_get_left hsA hlt, Orb.unpack_get hlt, h1 i hlt]
  · obtain ⟨t, rfl⟩ : ∃ t, i = n + t := ⟨i - n, by omega⟩
    have ht : t < n := by omega
    rw [dbl_get_right hsA hsB ht, Orb.unpack_get ht, h2 t ht]

theorem dbl_unpack {A B P : Nat} (h : pairK A B P = true) :
    dbl 480 (unpack 480 9 A) (unpack 480 9 B) = unpack 960 10 P := by
  unfold pairK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  exact dbl_unpack_of (n := 480) (fun i hi => Nat.eq_of_beq_eq_true (allN_spec h1 i hi))
    (fun i hi => Nat.eq_of_beq_eq_true (allN_spec h2 i hi))

theorem resLift_bind {e : LiftEntry} (hl : e.words.length = 3) :
    (resLift e).size = 3 ∧ ∀ j < 3, (resLift e)[j]! = unpack 480 9 (imgK e j) ∧
      canonK 480 9 (mask 9) (480 * 9) (imgK e j) = true := by
  refine ⟨by simp [resLift, hl], fun j hj => ?_⟩
  have hjl : j < e.words.length := by rw [hl]; exact hj
  have e1 : (resLift e)[j]! = posArr 480 resArrs (e.words.getD j []) := by
    rw [resLift, getElem!_pos _ _ (by simpa using hjl), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hjl]
  rw [e1]
  exact posArr_res _

theorem peq_self (n : Nat) (t : Array Nat) : peq n t t = true := by
  rw [peq, allBelowN_iff]
  intro i _
  exact beq_self_eq_true _

theorem resQPow_unpack : ∀ p : Nat, resQPow p = unpack 480 9 (qPowK p) ∧
    canonK 480 9 (mask 9) (480 * 9) (qPowK p) = true
  | 0 => ⟨by change idA 480 = unpack 480 9 (pidn 480 9); rw [idK_sound idK9], canonI9⟩
  | p + 1 => by
    obtain ⟨ih1, ih2⟩ := resQPow_unpack p
    have hq := posArr_res liftData.qWord
    rw [liftData_eq, qW_eq] at hq
    have e1 : resQPow (p + 1) = compA 480 resQ (resQPow p) := rfl
    rw [e1, resQ, liftData_eq, qW_eq, hq.1, ih1]
    exact ⟨compA_unpack hq.2 ih2, canonK_pcomp hq.2 ih2⟩

theorem graph_of {k i : Nat} {P : Nat → Nat} (hk : graphK (liftK k i) P = true)
    (hc : ((resPair (liftAt k i)).size = 3 ∧
      ∀ j < 3, (resPair (liftAt k i))[j]! = unpack 960 10 (P j)) →
      CFSG.Sporadic.HNOddCore.chainCheck 960 (resPair (liftAt k i)) resW resBase2 resSizes = true) :
    liftGraphOK (liftAt k i) = true := by
  rw [← liftAt_eq] at hk
  unfold graphK at hk
  simp only [bAnd_iff] at hk
  obtain ⟨hl, hb, hq⟩ := hk
  have hl' : (liftAt k i).words.length = 3 := Nat.eq_of_beq_eq_true hl
  obtain ⟨hs, hg⟩ := resLift_bind hl'
  have hO : (resPair (liftAt k i)).size = 3 ∧
      ∀ j < 3, (resPair (liftAt k i))[j]! = unpack 960 10 (P j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    have e : (resPair (liftAt k i))[j]! = dbl 480 resArrs[j]! (resLift (liftAt k i))[j]! := by
      interval_cases j <;> rfl
    rw [e, resArrs_bind.2 j hj, (hg j hj).1]
    exact dbl_unpack (allN_spec hb j hj)
  unfold liftGraphOK
  rw [Bool.and_eq_true]
  refine ⟨hc hO, ?_⟩
  have hp := posArr_unpack idK9 canonI9 hs hg liftData.qWord
  rw [hp.1, (resQPow_unpack _).1, liftData_eq, qW_eq, Nat.eq_of_beq_eq_true hq]
  exact peq_self _ _

theorem hn960 : 0 < 960 ∧ 960 + 1 < 2 ^ 10 ∧ 960 < 65536 := by norm_num

theorem g0_0 : liftGraphOK (liftAt 0 0) = true := graph_of (P := PP0_0.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP0_0.head PP0_0.hl (by norm_num)
    PP0_0.hs (by quickRfl) (by decide +kernel)
theorem g0_1 : liftGraphOK (liftAt 0 1) = true := graph_of (P := PP0_1.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP0_1.head PP0_1.hl (by norm_num)
    PP0_1.hs (by quickRfl) (by decide +kernel)
theorem g0_2 : liftGraphOK (liftAt 0 2) = true := graph_of (P := PP0_2.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP0_2.head PP0_2.hl (by norm_num)
    PP0_2.hs (by quickRfl) (by decide +kernel)
theorem g0_3 : liftGraphOK (liftAt 0 3) = true := graph_of (P := PP0_3.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP0_3.head PP0_3.hl (by norm_num)
    PP0_3.hs (by quickRfl) (by decide +kernel)
theorem g3_0 : liftGraphOK (liftAt 3 0) = true := graph_of (P := PP3_0.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP3_0.head PP3_0.hl (by norm_num)
    PP3_0.hs (by quickRfl) (by decide +kernel)
theorem g3_1 : liftGraphOK (liftAt 3 1) = true := graph_of (P := PP3_1.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP3_1.head PP3_1.hl (by norm_num)
    PP3_1.hs (by quickRfl) (by decide +kernel)
theorem g3_2 : liftGraphOK (liftAt 3 2) = true := graph_of (P := PP3_2.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP3_2.head PP3_2.hl (by norm_num)
    PP3_2.hs (by quickRfl) (by decide +kernel)
theorem g3_3 : liftGraphOK (liftAt 3 3) = true := graph_of (P := PP3_3.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP3_3.head PP3_3.hl (by norm_num)
    PP3_3.hs (by quickRfl) (by decide +kernel)
theorem g9_0 : liftGraphOK (liftAt 9 0) = true := graph_of (P := PP9_0.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP9_0.head PP9_0.hl (by norm_num)
    PP9_0.hs (by quickRfl) (by decide +kernel)
theorem g9_1 : liftGraphOK (liftAt 9 1) = true := graph_of (P := PP9_1.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP9_1.head PP9_1.hl (by norm_num)
    PP9_1.hs (by quickRfl) (by decide +kernel)
theorem g9_2 : liftGraphOK (liftAt 9 2) = true := graph_of (P := PP9_2.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP9_2.head PP9_2.hl (by norm_num)
    PP9_2.hs (by quickRfl) (by decide +kernel)
theorem g9_3 : liftGraphOK (liftAt 9 3) = true := graph_of (P := PP9_3.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP9_3.head PP9_3.hl (by norm_num)
    PP9_3.hs (by quickRfl) (by decide +kernel)
theorem g10_0 : liftGraphOK (liftAt 10 0) = true := graph_of (P := PP10_0.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP10_0.head PP10_0.hl (by norm_num)
    PP10_0.hs (by quickRfl) (by decide +kernel)
theorem g10_1 : liftGraphOK (liftAt 10 1) = true := graph_of (P := PP10_1.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP10_1.head PP10_1.hl (by norm_num)
    PP10_1.hs (by quickRfl) (by decide +kernel)
theorem g10_2 : liftGraphOK (liftAt 10 2) = true := graph_of (P := PP10_2.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP10_2.head PP10_2.hl (by norm_num)
    PP10_2.hs (by quickRfl) (by decide +kernel)
theorem g10_3 : liftGraphOK (liftAt 10 3) = true := graph_of (P := PP10_3.S) (by quickRfl) fun hO =>
  chainCheck_of hO rfl w0 wD hn960 (base2_of (by quickRfl)) PP10_3.head PP10_3.hl (by norm_num)
    PP10_3.hs (by quickRfl) (by decide +kernel)

theorem lifts_len : localCert.records.map (fun r => r.lifts.length) =
    [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0] := by
  rw [localCert_eq]
  decide +kernel

theorem graph_at : ∀ k < 12, ∀ i < [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0].getD k 0,
    liftGraphOK (liftAt k i) = true := by
  intro k hk i hi
  interval_cases k <;> simp only [List.getD_cons_succ, List.getD_cons_zero] at hi
  · interval_cases i
    exacts [g0_0, g0_1, g0_2, g0_3]
  · omega
  · omega
  · interval_cases i
    exacts [g3_0, g3_1, g3_2, g3_3]
  · omega
  · omega
  · omega
  · omega
  · omega
  · interval_cases i
    exacts [g9_0, g9_1, g9_2, g9_3]
  · interval_cases i
    exacts [g10_0, g10_1, g10_2, g10_3]
  · omega

theorem graph_all : localCert.records.all (fun r => r.lifts.all liftGraphOK) = true := by
  have hlen12 : localCert.records.length = 12 := by
    simpa using congrArg List.length lifts_len
  rw [List.all_eq_true]
  intro r hr
  rw [List.all_eq_true]
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hlen : (localCert.records.map (fun r => r.lifts.length)).getD k 0 =
      [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0].getD k 0 := by
    rw [lifts_len]
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map] at hlen
  have hat : liftAt k i = localCert.records[k].lifts[i] := by
    simp only [liftAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      Option.getD_some, List.getElem?_eq_getElem hi]
  rw [← hat]
  exact graph_at k (by omega) i (by omega)

theorem facts2122 : liftResOK (wordArrs Data.MWords) = true ∧
    localCert.records.all (fun r => r.lifts.all liftGraphOK) = true :=
  ⟨res_ok, graph_all⟩

end CertificateChecks.KernelSpor.ON2122

end
