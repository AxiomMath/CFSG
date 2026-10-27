module

public import Certificates.Kernel.Sporadic.OddCore.HN2092C
public import Certificates.Kernel.Sporadic.OddCore.HN2091
public import Certificates.Kernel.Sporadic.OddCore.HN2089
public import CFSG.Certificates.Kernel.Spor.SubOrbSound
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.Spor.PWord
import Mathlib.Tactic.IntervalCases
import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2092

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.HNSchreier.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.BfsPin CFSG.KS.PEnum CFSG.KS.BfsL CFSG.KS.SubOrb CertificateChecks.KernelSpor.HND

theorem unpack_get' {n w P x : Nat} (hx : x < n) : (unpack n w P)[x]! = pg w (mask w) P x := by
  unfold unpack
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem range_of_canonG {n w G : Nat} (h : canonK n w (mask w) (n * w) G = true) :
    ∀ x < n, pg w (mask w) G x < n := by
  unfold canonK at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  intro x hx
  exact Eq.mp Nat.blt_eq (allN_spec ((bAnd_iff _ _).1 h2).2 x hx)

theorem shift_of_canonG {n w G : Nat} (h : canonK n w (mask w) (n * w) G = true) :
    Nat.shiftRight G (n * w) = 0 := by
  unfold canonK at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h2).1

theorem range_of_canon {G : Nat} (h : canonK 1100 11 (mask 11) (1100 * 11) G = true) :
    ∀ x < 1100, pg 11 (mask 11) G x < 1100 := range_of_canonG h

theorem shift_of_canon {G : Nat} (h : canonK 1100 11 (mask 11) (1100 * 11) G = true) :
    Nat.shiftRight G (1100 * 11) = 0 := shift_of_canonG h

theorem kI : canonK 1100 11 (mask 11) (1100 * 11) (pidn 1100 11) = true := by quickRfl
theorem kid : idK 1100 11 (mask 11) = true := by quickRfl

@[expose] noncomputable def siG (g : Nat) : Nat := pinvS 1100 11 (mask 11) (HSG g)

@[expose] noncomputable def ppK (P e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 1100 11)
    (fun _ acc => CFSG.KC.Enum.pcomp 1100 11 (mask 11) acc P) e

theorem ppow_unpack {P : Nat} (hP : canonK 1100 11 (mask 11) (1100 * 11) P = true) :
    ∀ e, ppow 1100 (unpack 1100 11 P) e = unpack 1100 11 (ppK P e) ∧
      canonK 1100 11 (mask 11) (1100 * 11) (ppK P e) = true
  | 0 => by
    refine ⟨?_, kI⟩
    change idA 1100 = unpack 1100 11 (pidn 1100 11)
    rw [idK_sound kid]
  | e + 1 => by
    obtain ⟨h1, h2⟩ := ppow_unpack hP e
    refine ⟨?_, canonK_pcomp h2 hP⟩
    change compA 1100 (ppow 1100 (unpack 1100 11 P) e) (unpack 1100 11 P) =
      unpack 1100 11 (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (ppK P e) P)
    rw [h1]
    exact compA_unpack h2 hP

theorem dk : allN 1100 (fun i => bAnd(Nat.blt (r32 HO6_1.PTS i) 8800,
    Nat.beq (r32 HO6_1.POS (r32 HO6_1.PTS i)) i)) = true := by quickRfl

theorem gk : allN 12 (fun s => allN 1100 (fun i => bAnd(Nat.blt (pg 11 (mask 11) (HSG s) i) 1100,
    Nat.beq (HN2091.genL 8800 HS6R s (r32 HO6_1.PTS i))
      (r32 HO6_1.PTS (pg 11 (mask 11) (HSG s) i))))) = true := by quickRfl

theorem gC : allN 12 (fun s => canonK 1100 11 (mask 11) (1100 * 11) (HSG s)) = true := by quickRfl
theorem gCI : allN 12 (fun s => canonK 1100 11 (mask 11) (1100 * 11) (siG s)) = true := by quickRfl
theorem gP : allN 12 (fun s => permOK 1100 11 (mask 11) (1100 * 11) (HSG s) (siG s)) = true := by
  quickRfl

theorem om0L_eq : om0L = Array.ofFn (n := 1100) fun i => r32 HO6_1.PTS i.val := HN2091.o6_1

theorem pt_lt {i : Nat} (hi : i < 1100) : r32 HO6_1.PTS i < 8800 :=
  Eq.mp Nat.blt_eq ((bAnd_iff _ _).1 (allN_spec dk i hi)).1

theorem pt_pos {i : Nat} (hi : i < 1100) : r32 HO6_1.POS (r32 HO6_1.PTS i) = i :=
  Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec dk i hi)).2

theorem om0L_size : om0L.size = 1100 := by rw [om0L_eq, Array.size_ofFn]

theorem om0L_get {i : Nat} (hi : i < 1100) : om0L[i]! = r32 HO6_1.PTS i := by
  rw [om0L_eq]
  exact CFSG.KS.PW.ofFn_get' hi

theorem pos_get {j : Nat} (hj : j < 1100) : (posArr 8800 om0L)[r32 HO6_1.PTS j]! = j := by
  have hR : ∀ i < om0L.size, om0L[i]! < 8800 := fun i hi => by
    rw [om0L_size] at hi
    rw [om0L_get hi]
    exact pt_lt hi
  have hd : ∀ i < om0L.size, ∀ j < i, om0L[j]! ≠ om0L[i]! := fun i hi j hji heq => by
    rw [om0L_size] at hi
    rw [om0L_get (by omega), om0L_get hi] at heq
    have e := congrArg (r32 HO6_1.POS) heq
    rw [pt_pos (by omega), pt_pos hi] at e
    omega
  have h := (CFSG.KS.PW.posArr_spec hR hd).2 j (by rw [om0L_size]; exact hj)
  rwa [om0L_get hj] at h

theorem g_get : om0Gens.size = 12 ∧ ∀ s < 12, om0Gens[s]! = unpack 1100 11 (HSG s) := by
  obtain ⟨h6s, h6⟩ := HN2091.s6G
  refine ⟨by unfold om0Gens; rw [Array.size_map, h6s], fun s hs => ?_⟩
  unfold om0Gens
  rw [getElem!_pos _ s (by rw [Array.size_map, h6s]; exact hs), Array.getElem_map,
    ← getElem!_pos InvData.s6Perms s (by rw [h6s]; exact hs)]
  unfold restrictTab
  refine (CFSG.KS.PW.arr_ext (n := 1100) (F := fun i => pg 11 (mask 11) (HSG s) i)
    (by rw [Array.size_map, om0L_size]) (fun i hi => ?_)).trans rfl
  · rw [getElem!_pos _ i (by rw [Array.size_map, om0L_size]; exact hi), Array.getElem_map,
      ← getElem!_pos om0L i (by rw [om0L_size]; exact hi), om0L_get hi, h6 s hs _ (pt_lt hi)]
    obtain ⟨hb1, hb2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec gk s hs) i hi)
    rw [Nat.eq_of_beq_eq_true hb2, pos_get (Eq.mp Nat.blt_eq hb1)]

theorem g_inv (g : Nat) (hg : g < 12) : pinvCand 1100 om0Gens[g]! = unpack 1100 11 (siG g) := by
  rw [g_get.2 g hg, HN2089.pinvCand_eq]
  exact invCand_unpack (allN_spec gP g hg)

theorem wa_k : wordEqK 1100 11 (mask 11) (pidn 1100 11) HSG siG 12 SixData.wa (HSX 0) = true := by
  quickRfl
theorem wb_k : wordEqK 1100 11 (mask 11) (pidn 1100 11) HSG siG 12 SixData.wb (HSX 1) = true := by
  quickRfl
theorem xC : allN 2 (fun i => canonK 1100 11 (mask 11) (1100 * 11) (HSX i)) = true := by quickRfl
theorem dC : allN 9 (fun j => canonK 1100 11 (mask 11) (1100 * 11) (HSD.S j)) = true := by quickRfl
theorem dP : allN 9 (fun j => permOK 1100 11 (mask 11) (1100 * 11) (HSD.S j)
    (pinvS 1100 11 (mask 11) (HSD.S j))) = true := by quickRfl
theorem dPC : allN 9 (fun j => permOK 1100 11 (mask 11) (1100 * 11) (HSD.S j) (HSD.SI j)) = true := by
  quickRfl
theorem ea_k : Nat.beq (ppK (HSX 0) SixData.ea) (HSD.S 0) = true := by quickRfl
theorem eb_k : Nat.beq (ppK (HSX 1) SixData.eb) (HSD.S 1) = true := by quickRfl

theorem x_get {wd : List Int} {r : Nat}
    (h : wordEqK 1100 11 (mask 11) (pidn 1100 11) HSG siG 12 wd r = true) :
    pword 1100 om0Gens (pinvs 1100 om0Gens) wd = unpack 1100 11 r := by
  rw [HN2089.pword_eq_wordA, HN2089.pinvs_eq_rawInvs]
  exact (wordEqK_sound g_get gP h).1

theorem a_eq : dA om0Gens = unpack 1100 11 (HSD.S 0) := by
  have h1 : dA om0Gens = ppow 1100 (unpack 1100 11 (HSX 0)) SixData.ea := by
    unfold dA
    rw [x_get wa_k]
  have h2 := (ppow_unpack (allN_spec xC 0 (by omega)) SixData.ea).1
  have h3 := Nat.eq_of_beq_eq_true ea_k
  rw [h1, h2, h3]

theorem b_eq : dB om0Gens = unpack 1100 11 (HSD.S 1) := by
  have h1 : dB om0Gens = ppow 1100 (unpack 1100 11 (HSX 1)) SixData.eb := by
    unfold dB
    rw [x_get wb_k]
  have h2 := (ppow_unpack (allN_spec xC 1 (by omega)) SixData.eb).1
  have h3 := Nat.eq_of_beq_eq_true eb_k
  rw [h1, h2, h3]

theorem cA : canonK 1100 11 (mask 11) (1100 * 11) (HSD.S 0) = true := allN_spec dC 0 (by omega)
theorem cB : canonK 1100 11 (mask 11) (1100 * 11) (HSD.S 1) = true := allN_spec dC 1 (by omega)

@[reducible, expose] noncomputable def pAB : Nat := CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSD.S 0) (HSD.S 1)

theorem o1 : Nat.beq (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSD.S 0) (HSD.S 0)) (pidn 1100 11) =
    true := by quickRfl
theorem o2 : Bool.not (Nat.beq (HSD.S 0) (pidn 1100 11)) = true := by quickRfl
theorem o3 : Nat.beq (ppK (HSD.S 1) 5) (pidn 1100 11) = true := by quickRfl
theorem o4 : Bool.not (Nat.beq (HSD.S 1) (pidn 1100 11)) = true := by quickRfl
theorem o5 : Nat.beq (ppK pAB 11) (pidn 1100 11) = true := by quickRfl
theorem o6 : Bool.not (Nat.beq pAB (pidn 1100 11)) = true := by quickRfl
theorem o7 : Bool.not (Nat.beq pAB (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSD.S 1) (HSD.S 0))) =
    true := by quickRfl

@[reducible, expose] noncomputable def O2 : Array (Array Nat) := #[unpack 1100 11 (HSD.S 0), unpack 1100 11 (HSD.S 1)]

theorem o2_get : O2.size = 2 ∧ ∀ j < 2, O2[j]! = unpack 1100 11 (HSD.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j <;> rfl

theorem bD : allN 4 (fun t => Nat.beq (pg 11 (mask 11) HSD.BP t)
    ((SixData.dBase.map Fin.val).toArray[t]!)) = true := by quickRfl

theorem dBase_ok : (SixData.dBase.map Fin.val).toArray.size = 4 ∧
    ∀ t < 4, (SixData.dBase.map Fin.val).toArray[t]! = pg 11 (mask 11) HSD.BP t :=
  HN2089.base_of (by decide +kernel) bD

theorem chD : chainCheck 1100 O2 SixData.dWords SixData.dBase SixData.dSizes = true :=
  chainCheck_of o2_get (by decide +kernel) (by decide +kernel)
    (by simp only [dD, Array.toArray_toList]) (by norm_num) dBase_ok HSD.head HSD.hl
    (by decide +kernel) HSD.hs dPC (by decide +kernel)

theorem strong_get : (CFSG.Sporadic.HNOddCore.strongArrs 1100 O2 SixData.dWords).size = 9 ∧
    ∀ j < 9, (CFSG.Sporadic.HNOddCore.strongArrs 1100 O2 SixData.dWords)[j]! = unpack 1100 11 (HSD.S j) := by
  have hSe : CFSG.Sporadic.HNOddCore.strongArrs 1100 O2 SixData.dWords =
      (CFSG.YGroups.ModelNative.strongOf 1100 O2 dD.toArray).1 := by
    unfold CFSG.Sporadic.HNOddCore.strongArrs
    rw [o2_get.1]
    simp only [dD, Array.toArray_toList]
  rw [hSe]
  exact strongOf_bind o2_get HSD.head

theorem bnd : Binds 1100 11 HSD.S 9 4 HSD.BP (CFSG.Sporadic.HNOddCore.strongArrs 1100 O2 SixData.dWords) dBaseArr :=
  ⟨by norm_num, by norm_num, by norm_num, strong_get.1, strong_get.2, dBase_ok.1, dBase_ok.2⟩

theorem sift_eq {G : Nat} (hG : canonK 1100 11 (mask 11) (1100 * 11) G = true) :
    siftA 1100 (dLevels (unpack 1100 11 (HSD.S 0)) (unpack 1100 11 (HSD.S 1))) dBaseArr 0
      (unpack 1100 11 G) =
      siftK 1100 11 (mask 11) (1100 * 11) (pidn 1100 11) HSD.LR HSD.TRI HSD.BP 4 0 G :=
  siftK_eq bnd dPC HSD.hl rfl (shift_of_canon hG) (range_of_canonK hG)

theorem o2_gens : O2.size = 2 ∧ ∀ s < 2, ∀ x < 1100, (O2[s]!)[x]! = pg 11 (mask 11) (HSD.S s) x :=
  ⟨rfl, fun s hs x hx => by rw [o2_get.2 s hs, unpack_get' hx]⟩

theorem imgs_of {k : Nat} {F : Nat → Nat}
    (h : ∀ s < k, canonK 1100 11 (mask 11) (1100 * 11) (F s) = true) :
    ∀ s < k, ∀ x < 1100, pg 11 (mask 11) (F s) x < 1100 :=
  fun s hs x hx => range_of_canon (h s hs) x hx

theorem hdO : bfsLHdK 1100 0 HSO.cnt HSO.PTS HSO.POS HSO.PAR HSO.LAB = true := by quickRfl
theorem slO : bfsLSlK 1100 HSO.cnt 2 (fun s x => pg 11 (mask 11) (HSD.S s) x) HSO.PTS HSO.POS
    HSO.PAR HSO.LAB 0 1100 = true := by quickRfl

theorem ptsO : ∀ j < HSO.cnt, bfsLPtK 1100 HSO.cnt 2 (fun s x => pg 11 (mask 11) (HSD.S s) x)
    HSO.PTS HSO.POS HSO.PAR HSO.LAB j = true := fun j hj =>
  HN2091.pts_of slO j (Nat.zero_le _) (by have e : HSO.cnt = 1100 := rfl; omega) hj

theorem bfsO : bfsList 1100 O2 0 = Array.ofFn (n := HSO.cnt) fun i => r32 HSO.PTS i.val :=
  bfsLK_sound o2_gens hdO ptsO

theorem orbO : orbitOK 1100 O2 (bfsList 1100 O2 0) = true := by
  rw [bfsO]
  exact orbitOK_sound o2_gens (imgs_of fun s hs => allN_spec dC s (by omega)) hdO ptsO

@[expose] noncomputable def Hc : Array (Array Nat) :=
  ((List.range 7).map fun i => unpack 1100 11 (HSD.S (i + 2))).toArray

theorem fz : (List.range 9).filter (fun j => Nat.beq (pg 11 (mask 11) (HSD.S j) 0) 0) =
    (List.range 7).map (· + 2) := by decide +kernel

theorem strong_list : CFSG.Sporadic.HNOddCore.strongArrs 1100 O2 SixData.dWords =
    ((List.range 9).map fun j => unpack 1100 11 (HSD.S j)).toArray := by
  apply Array.ext
  · rw [strong_get.1]
    simp
  · intro j h1 h2
    have hj : j < 9 := by rw [strong_get.1] at h1; exact h1
    rw [← getElem!_pos _ j h1, strong_get.2 j hj]
    simp

theorem stab_eq : dStab (unpack 1100 11 (HSD.S 0)) (unpack 1100 11 (HSD.S 1)) = Hc := by
  unfold dStab
  rw [strong_list, List.filter_toArray, List.filter_map]
  unfold Hc
  apply congrArg List.toArray
  have e : ((fun s : Array Nat => s[0]! == 0) ∘ fun j => unpack 1100 11 (HSD.S j)) =
      fun j => Nat.beq (pg 11 (mask 11) (HSD.S j) 0) 0 := by
    funext j
    simp only [Function.comp, unpack_get' (by norm_num : 0 < 1100)]
    rw [Bool.eq_iff_iff, beq_iff_eq]
    exact ⟨fun h => by rw [h]; rfl, fun h => Nat.eq_of_beq_eq_true h⟩
  rw [e, fz, List.map_map]
  simp only [Function.comp_def]

theorem hc_size : Hc.size = 7 := by simp [Hc]

theorem hc_get {i : Nat} (hi : i < 7) : Hc[i]! = unpack 1100 11 (HSD.S (i + 2)) := by
  unfold Hc
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem hc_gens : Hc.size = 7 ∧ ∀ s < 7, ∀ x < 1100,
    (Hc[s]!)[x]! = pg 11 (mask 11) (HSD.S (s + 2)) x :=
  ⟨hc_size, fun s hs x hx => by rw [hc_get hs, unpack_get' hx]⟩

theorem hk : allN 7 (fun i => bAnd(Nat.beq (pg 11 (mask 11) (HSD.S (i + 2)) 0) 0,
    siftK 1100 11 (mask 11) (1100 * 11) (pidn 1100 11) HSD.LR HSD.TRI HSD.BP 4 0
      (HSD.S (i + 2)))) = true := by quickRfl

theorem c15 : (allBelowN Hc.size fun i => (Hc[i]!)[0]! == 0 &&
    pisInv 1100 Hc[i]! (pinvCand 1100 Hc[i]!) &&
    siftA 1100 (dLevels (unpack 1100 11 (HSD.S 0)) (unpack 1100 11 (HSD.S 1))) dBaseArr 0
      Hc[i]!) = true := by
  rw [allBelowN_iff, hc_size]
  intro i hi
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hk i hi)
  have hp := allN_spec dP (i + 2) (by omega)
  rw [hc_get hi, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [unpack_get' (by norm_num : 0 < 1100)]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h1)
  · rw [HN2089.pisInv_eq, HN2089.pinvCand_eq, invCand_unpack hp]
    exact (invEqK_sound hp).2
  · rw [sift_eq (allN_spec dC (i + 2) (by omega))]
    exact h2

@[expose] noncomputable def ptS (i q : Nat) : Nat :=
  nIf(Nat.beq i 0, r32 HSL0.PTS q, nIf(Nat.beq i 1, r32 HSL1.PTS q, nIf(Nat.beq i 2,
    r32 HSL2.PTS q, nIf(Nat.beq i 3, r32 HSL3.PTS q, r32 HSL4.PTS q))))

@[expose] noncomputable def cntS (i : Nat) : Nat :=
  nIf(Nat.beq i 0, HSL0.cnt, nIf(Nat.beq i 1, HSL1.cnt, nIf(Nat.beq i 2, HSL2.cnt,
    nIf(Nat.beq i 3, HSL3.cnt, HSL4.cnt))))

@[expose] noncomputable def LH (s x : Nat) : Nat := pg 11 (mask 11) (HSD.S (s + 2)) x

theorem hd0 : bfsLHdK 1100 (r32 HSL0.PTS 0) HSL0.cnt HSL0.PTS HSL0.POS HSL0.PAR HSL0.LAB = true := by
  quickRfl
theorem hd1 : bfsLHdK 1100 (r32 HSL1.PTS 0) HSL1.cnt HSL1.PTS HSL1.POS HSL1.PAR HSL1.LAB = true := by
  quickRfl
theorem hd2 : bfsLHdK 1100 (r32 HSL2.PTS 0) HSL2.cnt HSL2.PTS HSL2.POS HSL2.PAR HSL2.LAB = true := by
  quickRfl
theorem hd3 : bfsLHdK 1100 (r32 HSL3.PTS 0) HSL3.cnt HSL3.PTS HSL3.POS HSL3.PAR HSL3.LAB = true := by
  quickRfl
theorem hd4 : bfsLHdK 1100 (r32 HSL4.PTS 0) HSL4.cnt HSL4.PTS HSL4.POS HSL4.PAR HSL4.LAB = true := by
  quickRfl

theorem sl0 : bfsLSlK 1100 HSL0.cnt 7 LH HSL0.PTS HSL0.POS HSL0.PAR HSL0.LAB 0 1 = true := by
  quickRfl
theorem sl1 : bfsLSlK 1100 HSL1.cnt 7 LH HSL1.PTS HSL1.POS HSL1.PAR HSL1.LAB 0 336 = true := by
  quickRfl
theorem sl2 : bfsLSlK 1100 HSL2.cnt 7 LH HSL2.PTS HSL2.POS HSL2.PAR HSL2.LAB 0 105 = true := by
  quickRfl
theorem sl3 : bfsLSlK 1100 HSL3.cnt 7 LH HSL3.PTS HSL3.POS HSL3.PAR HSL3.LAB 0 630 = true := by
  quickRfl
theorem sl4 : bfsLSlK 1100 HSL4.cnt 7 LH HSL4.PTS HSL4.POS HSL4.PAR HSL4.LAB 0 28 = true := by
  quickRfl

theorem imgH : ∀ s < 7, ∀ x < 1100, LH s x < 1100 :=
  fun s hs x hx => range_of_canon (allN_spec dC (s + 2) (by omega)) x hx

theorem orb_i : ∀ i < 5, bfsList 1100 Hc (ptS i 0) =
      (Array.ofFn (n := cntS i) fun q => ptS i q.val) ∧
    orbitOK 1100 Hc (Array.ofFn (n := cntS i) fun q => ptS i q.val) = true := by
  intro i hi
  interval_cases i
  · have hp := fun j hj => HN2091.pts_of sl0 j (Nat.zero_le _)
      (by have e : HSL0.cnt = 1 := rfl; omega) hj
    exact ⟨bfsLK_sound hc_gens hd0 hp, orbitOK_sound hc_gens imgH hd0 hp⟩
  · have hp := fun j hj => HN2091.pts_of sl1 j (Nat.zero_le _)
      (by have e : HSL1.cnt = 336 := rfl; omega) hj
    exact ⟨bfsLK_sound hc_gens hd1 hp, orbitOK_sound hc_gens imgH hd1 hp⟩
  · have hp := fun j hj => HN2091.pts_of sl2 j (Nat.zero_le _)
      (by have e : HSL2.cnt = 105 := rfl; omega) hj
    exact ⟨bfsLK_sound hc_gens hd2 hp, orbitOK_sound hc_gens imgH hd2 hp⟩
  · have hp := fun j hj => HN2091.pts_of sl3 j (Nat.zero_le _)
      (by have e : HSL3.cnt = 630 := rfl; omega) hj
    exact ⟨bfsLK_sound hc_gens hd3 hp, orbitOK_sound hc_gens imgH hd3 hp⟩
  · have hp := fun j hj => HN2091.pts_of sl4 j (Nat.zero_le _)
      (by have e : HSL4.cnt = 28 := rfl; omega) hj
    exact ⟨bfsLK_sound hc_gens hd4 hp, orbitOK_sound hc_gens imgH hd4 hp⟩

theorem part : subOrbK 1100 5 cntS ptS (r32 HSLB) (r32 HSPN) = true := by quickRfl

theorem partA : allN 1100 (fun p => bAnd(Nat.blt (r32 HSLB p) 5,
    bAnd(Nat.blt (r32 HSPN p) (cntS (r32 HSLB p)), Nat.beq (ptS (r32 HSLB p) (r32 HSPN p)) p))) =
    true := by quickRfl

theorem partB : allN 5 (fun i => allN (cntS i) (fun q => bAnd(Nat.blt (ptS i q) 1100,
    Nat.beq (r32 HSLB (ptS i q)) i))) = true := by quickRfl

@[expose] noncomputable def Lsc : Array (Array Nat) :=
  Array.ofFn (n := 5) fun i => Array.ofFn (n := cntS i.val) fun q => ptS i q.val

@[expose] noncomputable def labc : Array Nat := Array.ofFn (n := 1100) fun p => r32 HSLB p.val

theorem sub_eq : subOrbits Hc = Lsc ∧ subLabels Lsc = labc :=
  subOrbK_sound (fun i hi => (orb_i i hi).1) part

theorem lsc_get {i : Nat} (hi : i < 5) :
    Lsc[i]! = Array.ofFn (n := cntS i) fun q => ptS i q.val := by
  unfold Lsc
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem labc_get {p : Nat} (hp : p < 1100) : labc[p]! = r32 HSLB p := CFSG.KS.PW.ofFn_get' hp

theorem ofFn_get2 {n x : Nat} {f : Nat → Nat} (hx : x < n) :
    (Array.ofFn (n := n) fun i => f i.val)[x]! = f x := CFSG.KS.PW.ofFn_get' hx

theorem c21 : (allBelowN 5 fun i => allBelowN (Lsc[i]!).size fun k =>
    labc[(Lsc[i]!)[k]!]! == i) = true := by
  rw [allBelowN_iff]
  intro i hi
  rw [allBelowN_iff, lsc_get hi, Array.size_ofFn]
  intro k hk
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec partB i hi) k hk)
  rw [ofFn_get2 hk, labc_get (Eq.mp Nat.blt_eq h5)]
  exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h6)

theorem c22 : (allBelowN 1100 fun p => decide (labc[p]! < 5) && (Lsc[labc[p]!]!).contains p) =
    true := by
  rw [allBelowN_iff]
  intro p hp
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 (allN_spec partA p hp)
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h3
  have hl : r32 HSLB p < 5 := Eq.mp Nat.blt_eq h2
  rw [labc_get hp, Bool.and_eq_true, decide_eq_true_eq, lsc_get hl]
  refine ⟨hl, ?_⟩
  rw [Array.contains_iff_mem, Array.mem_iff_getElem]
  refine ⟨r32 HSPN p, by rw [Array.size_ofFn]; exact Eq.mp Nat.blt_eq h4, ?_⟩
  rw [Array.getElem_ofFn]
  exact Nat.eq_of_beq_eq_true h5

theorem kc : allN 12 (fun g => bAnd(
    siftK 1100 11 (mask 11) (1100 * 11) (pidn 1100 11) HSD.LR HSD.TRI HSD.BP 4 0
      (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSG g)
        (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSD.S 0) (siG g))),
    siftK 1100 11 (mask 11) (1100 * 11) (pidn 1100 11) HSD.LR HSD.TRI HSD.BP 4 0
      (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSG g)
        (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSD.S 1) (siG g))))) = true := by quickRfl

theorem k5 : Bool.not (siftK 1100 11 (mask 11) (1100 * 11) (pidn 1100 11) HSD.LR HSD.TRI HSD.BP 4 0
    (HSG 5)) = true := by quickRfl

theorem conj_eq {g j : Nat} (hg : g < 12) (hj : j < 2) :
    pcomp 1100 om0Gens[g]! (pcomp 1100 (unpack 1100 11 (HSD.S j)) (pinvCand 1100 om0Gens[g]!)) =
      unpack 1100 11 (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSG g)
        (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSD.S j) (siG g))) := by
  have cg := allN_spec gC g hg
  have ci := allN_spec gCI g hg
  have cj := allN_spec dC j (by omega)
  rw [g_inv g hg, g_get.2 g hg, HN2089.pcomp_eq, HN2089.pcomp_eq, compA_unpack cj ci,
    compA_unpack cg (canonK_pcomp cj ci)]

theorem conj_canon {g j : Nat} (hg : g < 12) (hj : j < 2) :
    canonK 1100 11 (mask 11) (1100 * 11) (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSG g)
      (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSD.S j) (siG g))) = true :=
  canonK_pcomp (allN_spec gC g hg) (canonK_pcomp (allN_spec dC j (by omega)) (allN_spec gCI g hg))

theorem eqA_k {p q : Nat} (hp : canonK 1100 11 (mask 11) (1100 * 11) p = true)
    (hq : canonK 1100 11 (mask 11) (1100 * 11) q = true) :
    peq 1100 (unpack 1100 11 p) (unpack 1100 11 q) = Nat.beq p q := by
  rw [HN2089.peq_eq]
  exact eqA_unpack hp hq

theorem pid_k : pid 1100 = unpack 1100 11 (pidn 1100 11) := by
  rw [HN2089.pid_eq, idK_sound kid]

theorem pcomp_k {p q : Nat} (hp : canonK 1100 11 (mask 11) (1100 * 11) p = true)
    (hq : canonK 1100 11 (mask 11) (1100 * 11) q = true) :
    pcomp 1100 (unpack 1100 11 p) (unpack 1100 11 q) =
      unpack 1100 11 (CFSG.KC.Enum.pcomp 1100 11 (mask 11) p q) := by
  rw [HN2089.pcomp_eq]
  exact compA_unpack hp hq

theorem facts2092 : sixChecks = true := by
  unfold sixChecks sixChecksA sixChecksD
  rw [a_eq, b_eq, stab_eq, sub_eq.1, sub_eq.2]
  have cAB : canonK 1100 11 (mask 11) (1100 * 11) pAB = true := canonK_pcomp cA cB
  have cBA := canonK_pcomp cB cA
  unfold sixChecksH
  simp only [Bool.and_eq_true]
  and_intros
  · rw [g_get.1]
    rfl
  · rw [allBelowN_iff]
    intro g hg
    rw [g_get.2 g hg, HN2089.pisInv_eq, HN2089.pinvCand_eq, invCand_unpack (allN_spec gP g hg)]
    exact (invEqK_sound (allN_spec gP g hg)).2
  · decide +kernel
  · decide +kernel
  · rw [pid_k, pcomp_k cA cA, eqA_k (canonK_pcomp cA cA) kI]
    exact o1
  · rw [pid_k, eqA_k cA kI]
    exact o2
  · rw [pid_k, (ppow_unpack cB 5).1, eqA_k (ppow_unpack cB 5).2 kI]
    exact o3
  · rw [pid_k, eqA_k cB kI]
    exact o4
  · rw [pid_k, pcomp_k cA cB, (ppow_unpack cAB 11).1, eqA_k (ppow_unpack cAB 11).2 kI]
    exact o5
  · rw [pid_k, pcomp_k cA cB, eqA_k cAB kI]
    exact o6
  · rw [pcomp_k cA cB, pcomp_k cB cA, eqA_k cAB cBA]
    exact o7
  · exact chD
  · exact orbO
  · rw [bfsO, Array.size_ofFn]
    rfl
  · exact c15
  · unfold Lsc
    rw [Array.size_ofFn]
    rfl
  · decide +kernel
  · decide +kernel
  · rw [allBelowN_iff]
    intro i hi
    rw [lsc_get hi]
    exact (orb_i i hi).2
  · unfold labc
    rw [Array.size_ofFn]
    rfl
  · exact c21
  · exact c22
  · rw [allBelowN_iff]
    intro g hg
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kc g hg)
    rw [Bool.and_eq_true, conj_eq hg (by omega), conj_eq hg (by omega),
      sift_eq (conj_canon hg (by omega)), sift_eq (conj_canon hg (by omega))]
    exact ⟨h1, h2⟩
  · rw [g_get.2 5 (by omega), sift_eq (allN_spec gC 5 (by omega))]
    exact k5

end CertificateChecks.KernelSpor.HN2092

end
