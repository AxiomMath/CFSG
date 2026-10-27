module

public import Certificates.Kernel.McLAS.NGlue
public import Certificates.Kernel.McLAS.RecN
public import Certificates.Kernel.McLAS.Rec3AChk0
public import Certificates.Kernel.McLAS.Rec3AChk1
public import Certificates.Kernel.McLAS.Rec3AChk2
public import Certificates.Kernel.McLAS.Rec3AChk3
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.KS.McLAS

noncomputable abbrev pc (p q : Nat) : Nat := pcomp 275 9 (mask 9) p q

noncomputable abbrev cj (g gi x : Nat) : Nat := pc (pc g x) gi

@[expose] noncomputable def zK (q : Nat) : Bool :=
  strictB (A3.T q) fun z => bIf(atK R3A.cnt R3A.T AIn3A q z, anyYK NT.F NTI z,
    brK R3A.cnt R3A.T R3A.SRT z (r32 BrA q))

@[expose] noncomputable def tripK (t : Nat) : Bool :=
  bIf(bAnd(Nat.blt t 1000, bAnd(bIf(Nat.beq (Nat.div t 100) (Nat.mod (Nat.div t 10) 10), false, true),
    bAnd(bIf(Nat.beq (Nat.div t 100) (Nat.mod t 10), false, true),
      bIf(Nat.beq (Nat.mod (Nat.div t 10) 10) (Nat.mod t 10), false, true)))),
    strictB (r32 Trip t) fun q => bAnd(Nat.blt q NW.cnt,
      bAnd(Nat.beq (pg 4 (mask 4) (NW.T q) 0) (Nat.div t 100),
      bAnd(Nat.beq (pg 4 (mask 4) (NW.T q) 1) (Nat.mod (Nat.div t 10) 10),
        Nat.beq (pg 4 (mask 4) (NW.T q) 2) (Nat.mod t 10)))), true)

@[expose] noncomputable def cImg (i j l : Nat) : Nat :=
  cj (NTI (12 + j)) (NT.F (12 + j)) (cj (NT.F (12 + i)) (NTI (12 + i)) (TL.F (l + 7)))

@[expose] noncomputable def cwK (t : Nat) : Bool :=
  bIf(Nat.beq (Nat.div t 10) (Nat.mod t 10), true,
    strictB (r32 CW t) fun w => bAnd(Nat.blt (Nat.mod w 4) 4,
      brK A3.cnt A3.T A3.SRT (cImg (Nat.div t 10) (Nat.mod t 10) (Nat.mod w 4)) (Nat.div w 4)))

theorem k6109a : bAnd(allN 4 (fun j => bAnd(Nat.beq (A3.G j) McLAS.idK,
      Nat.beq (A3.GI j) (TL.F (Nat.add j 7)))),
    bAnd(penumHdK McLAS.idK A3.cnt 200 A3.T A3.PL,
    bAnd(recSlK true A3.G A3.GI 4 A3.cnt A3.T A3.PL A3.POS A3.SRT A3.SRI A3.HS A3.HSI 0 200,
    bAnd(allN 2 (fun j => bAnd(Nat.beq (R3A.G j) (CertificateChecks.KernelCensus.McLS.F j),
      bAnd(invEqK 275 9 (mask 9) (275 * 9) (R3A.G j) (R3A.GI j),
        bAnd(canonK 275 9 (mask 9) (275 * 9) (R3A.G j), canonK 275 9 (mask 9) (275 * 9) (R3A.GI j))))),
    bAnd(Nat.beq R3A.R (TT.F 0), bAnd(penumHdK (TT.F 0) R3A.cnt 30800 R3A.T R3A.PL,
      Nat.ble R3A.cnt 31000)))))) = true := by
  quickRfl

theorem k6109b : bAnd(szOK 10 4, bAnd(allN 2 (fun j => bAnd(Nat.beq (NW.G j) (pidn 10 4),
      bAnd(canonK 10 4 (mask 4) (10 * 4) (NW.GI j),
      bAnd(canonK 10 4 (mask 4) (10 * 4) (NWI j), invEqK 10 4 (mask 4) (10 * 4) (NW.GI j) (NWI j))))),
    bAnd(penumHdK (pidn 10 4) NW.cnt 800 NW.T NW.PL, bAnd(Nat.ble NW.cnt 1024,
    bAnd(penumSlK 10 4 (mask 4) (10 * 4) true NW.G NW.GI 2 NW.cnt NW.T NW.PL NW.POS NW.SRT NW.SRI 0 1024,
    bAnd(slK NW.cnt (hsortPtK 10 4 (mask 4) NW.cnt NW.T NW.HS NW.HSI) 0 1024,
    bAnd(allN 2 (fun k => allN 10 (fun i => firstK NT.F NTI
      (cj (NT.F (Nat.add 10 k)) (NTI (Nat.add 10 k)) (NT.F i)) (pg 4 (mask 4) (NW.GI k) i))),
      allN 1000 tripK))))))) = true := by
  quickRfl

theorem k6109c : bAnd(allN 10 (fun j => bAnd(atK R3A.cnt R3A.T YIn3A j (NT.F j),
      atK A3.cnt A3.T YInA j (NT.F j))),
    bAnd(Nat.beq (NT.F 0) (TT.F 0),
    bAnd(allN 10 (fun i => allN 10 (fun j => bIf(Nat.beq i j, true,
      bAnd(bIf(Nat.beq (NT.F i) (NT.F j), false, true), bIf(Nat.beq (NT.F i) (NTI j), false, true))))),
    bAnd(slK A3.cnt zK 0 200,
    bAnd(allN 2 (fun k => bAnd(sK (NT.F (Nat.add 10 k)),
      bAnd(allN 4 (fun l => atK A3.cnt A3.T NAInA (Nat.add (Nat.mul k 4) l)
        (cj (NT.F (Nat.add 10 k)) (NTI (Nat.add 10 k)) (TL.F (Nat.add l 7)))),
      allN 10 (fun i => anyYK NT.F NTI (cj (NT.F (Nat.add 10 k)) (NTI (Nat.add 10 k)) (NT.F i)))))),
    bAnd(allN 10 (fun i => bAnd(sK (NT.F (Nat.add 12 i)),
      Nat.beq (pc (NT.F (Nat.add 12 i)) (TT.F 0)) (pc (TT.F 0) (NT.F (Nat.add 12 i))))),
      allN 100 cwK)))))) = true := by
  quickRfl

theorem fa : (∀ j < 4, A3.G j = McLAS.idK ∧ A3.GI j = TL.F (j + 7)) ∧
    penumHdK McLAS.idK A3.cnt 200 A3.T A3.PL = true ∧
    recSlK true A3.G A3.GI 4 A3.cnt A3.T A3.PL A3.POS A3.SRT A3.SRI A3.HS A3.HSI 0 200 = true ∧
    (∀ j < 2, R3A.G j = CertificateChecks.KernelCensus.McLS.F j ∧
      invEqK 275 9 (mask 9) (275 * 9) (R3A.G j) (R3A.GI j) = true ∧ Cn (R3A.G j) ∧ Cn (R3A.GI j)) ∧
    R3A.R = TT.F 0 ∧ penumHdK (TT.F 0) R3A.cnt 30800 R3A.T R3A.PL = true ∧ R3A.cnt ≤ 31000 := by
  have h := k6109a
  simp only [bAnd_iff, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun j hj => ?_, h2, h3, fun j hj => ?_, h5, h6, h7⟩
  · have hj' := allN_spec h1 j hj
    simp only [bAnd_iff, Nat.beq_eq] at hj'
    exact hj'
  · have hj' := allN_spec h4 j hj
    simp only [bAnd_iff, Nat.beq_eq] at hj'
    exact hj'

theorem fb : szOK 10 4 = true ∧ (∀ j < 2, NW.G j = pidn 10 4 ∧
      canonK 10 4 (mask 4) (10 * 4) (NW.GI j) = true ∧ canonK 10 4 (mask 4) (10 * 4) (NWI j) = true ∧
      invEqK 10 4 (mask 4) (10 * 4) (NW.GI j) (NWI j) = true) ∧
    penumHdK (pidn 10 4) NW.cnt 800 NW.T NW.PL = true ∧ NW.cnt ≤ 1024 ∧
    penumSlK 10 4 (mask 4) (10 * 4) true NW.G NW.GI 2 NW.cnt NW.T NW.PL NW.POS NW.SRT NW.SRI 0 1024 =
      true ∧
    slK NW.cnt (hsortPtK 10 4 (mask 4) NW.cnt NW.T NW.HS NW.HSI) 0 1024 = true ∧
    (∀ k < 2, ∀ i < 10, firstK NT.F NTI (cj (NT.F (10 + k)) (NTI (10 + k)) (NT.F i))
      (pg 4 (mask 4) (NW.GI k) i) = true) ∧
    (∀ t < 1000, tripK t = true) := by
  have h := k6109b
  simp only [bAnd_iff, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, fun j hj => ?_, h3, h4, h5, h6, fun k hk i hi => allN_spec (allN_spec h7 k hk) i hi,
    fun t ht => allN_spec h8 t ht⟩
  have hj' := allN_spec h2 j hj
  simp only [bAnd_iff, Nat.beq_eq] at hj'
  exact hj'

theorem fc : (∀ j < 10, atK R3A.cnt R3A.T YIn3A j (NT.F j) = true ∧
      atK A3.cnt A3.T YInA j (NT.F j) = true) ∧ NT.F 0 = TT.F 0 ∧
    (∀ i < 10, ∀ j < 10, i ≠ j → NT.F i ≠ NT.F j ∧ NT.F i ≠ NTI j) ∧
    slK A3.cnt zK 0 200 = true ∧
    (∀ k < 2, sK (NT.F (10 + k)) = true ∧
      (∀ l < 4, atK A3.cnt A3.T NAInA (k * 4 + l) (cj (NT.F (10 + k)) (NTI (10 + k)) (TL.F (l + 7))) =
        true) ∧
      ∀ i < 10, anyYK NT.F NTI (cj (NT.F (10 + k)) (NTI (10 + k)) (NT.F i)) = true) ∧
    (∀ i < 10, sK (NT.F (12 + i)) = true ∧
      pc (NT.F (12 + i)) (TT.F 0) = pc (TT.F 0) (NT.F (12 + i))) ∧
    (∀ t < 100, cwK t = true) := by
  have h := k6109c
  simp only [bAnd_iff, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun j hj => ?_, h2, fun i hi j hj hij => ?_, h4, fun k hk => ?_, fun i hi => ?_,
    fun t ht => allN_spec h7 t ht⟩
  · have hj' := allN_spec h1 j hj
    simp only [bAnd_iff] at hj'
    exact hj'
  · have hj' := allN_spec (allN_spec h3 i hi) j hj
    have e : Nat.beq i j = false := Bool.eq_false_iff.2 fun h => hij (Nat.eq_of_beq_eq_true h)
    rw [e] at hj'
    obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 hj'
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, Nat.beq_refl] at a1
      exact absurd a1 (by decide)
    · rw [h, Nat.beq_refl] at a2
      exact absurd a2 (by decide)
  · have hk' := allN_spec h5 k hk
    obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 hk'
    obtain ⟨a2, a3⟩ := (bAnd_iff _ _).1 a2
    exact ⟨a1, fun l hl => allN_spec a2 l hl, fun i hi => allN_spec a3 i hi⟩
  · have hi' := allN_spec h6 i hi
    simp only [bAnd_iff, Nat.beq_eq] at hi'
    exact hi'

theorem all_of_get {A : Array Table} {m : Nat} {f : Nat → Table} {p : Table → Bool}
    (hs : A.size = m) (hf : ∀ k < m, A[k]! = f k) (h : ∀ k < m, p (f k) = true) :
    A.all p = true := by
  rw [Array.all_eq_true]
  intro k hk
  rw [← getElem!_pos A k hk, hf k (by omega)]
  exact h k (by omega)

theorem any_of_get {A : Array Table} {m : Nat} {f : Nat → Table} {p : Table → Bool}
    (hs : A.size = m) (hf : ∀ k < m, A[k]! = f k) {k : Nat} (hk : k < m) (h : p (f k) = true) :
    A.any p = true := by
  rw [Array.any_eq_true]
  refine ⟨k, by omega, ?_⟩
  rw [← getElem!_pos A k (by omega), hf k hk]
  exact h

theorem nrmN_get {k : Nat} (hk : k < 2) : nrmN[k]! = tabT (unpack 275 9 (NT.F (10 + k))) := by
  interval_cases k
  · exact tabNT (by norm_num)
  · exact tabNT (by norm_num)

theorem pg_get {j : Nat} (hj : j < 2) :
    mclPGTbls[j]! = tabT (unpack 275 9 (CertificateChecks.KernelCensus.McLS.F j)) := by
  rw [← mclStrongArrs_get j (by omega)]
  interval_cases j <;> rfl

theorem tabs_pg : TabsOK 275 9 2 R3A.G mclPGTbls := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [pg_get hj, (fa.2.2.2.1 j hj).1]
  exact ⟨rfl, (fa.2.2.2.1 j hj).1 ▸ (fa.2.2.2.1 j hj).2.2.1⟩

theorem tabs_pgi : TabsOK 275 9 2 R3A.GI mclPGInvTbls :=
  TabsOK_inv tabs_pg fun j hj => ⟨(fa.2.2.2.1 j hj).2.1, (fa.2.2.2.1 j hj).2.2.2⟩

theorem tabs_ag : TabsOK 275 9 4 A3.GI aGens3 := by
  refine ⟨aGens3_size, fun j hj => ?_⟩
  rw [aGens3_get hj, (fa.1 j hj).2]
  exact ⟨rfl, TLc (by omega)⟩

theorem a3_spec : (∀ i < A3.cnt, penumPtK 275 9 (mask 9) (275 * 9) true A3.G A3.GI 4 A3.cnt A3.T
      A3.PL A3.POS A3.SRT A3.SRI i = true) ∧
    (∀ i < A3.cnt, hsortPtK 275 9 (mask 9) A3.cnt A3.T A3.HS A3.HSI i = true) := by
  have hc : A3.cnt ≤ 200 * 1 := by
    have := fa.2.1
    unfold penumHdK at this
    simp only [bAnd_iff, Nat.ble_eq] at this
    omega
  refine rec_spec (cnt := A3.cnt) (NS := 1) hc fun s hs => ?_
  have hs0 : s = 0 := by omega
  subst hs0
  exact fa.2.2.1

theorem c3A_all : ∀ s < 155, c3A s = true :=
  join4 (a := 39) (b := 39) (c := 39) (d := 38) C3A0.all C3A1.all C3A2.all C3A3.all

theorem r3_spec : (∀ i < R3A.cnt, penumPtK 275 9 (mask 9) (275 * 9) true R3A.G R3A.GI 2 R3A.cnt
      R3A.T R3A.PL R3A.POS R3A.SRT R3A.SRI i = true) ∧
    (∀ i < R3A.cnt, hsortPtK 275 9 (mask 9) R3A.cnt R3A.T R3A.HS R3A.HSI i = true) :=
  rec_spec (cnt := R3A.cnt) (NS := 155) (by have := fa.2.2.2.2.2.2; omega) c3A_all

theorem nw_spec : (∀ i < NW.cnt, penumPtK 10 4 (mask 4) (10 * 4) true NW.G NW.GI 2 NW.cnt
      NW.T NW.PL NW.POS NW.SRT NW.SRI i = true) ∧
    (∀ i < NW.cnt, hsortPtK 10 4 (mask 4) NW.cnt NW.T NW.HS NW.HSI i = true) :=
  ⟨fun i hi => penumSl_spec fb.2.2.2.2.1 i (Nat.zero_le _) (by have := fb.2.2.2.1; omega) hi,
    fun i hi => slK_spec fb.2.2.2.2.2.1 i (Nat.zero_le _) (by have := fb.2.2.2.1; omega) hi⟩

theorem a3_canon {q : Nat} (hq : q < A3.cnt) : Cn (A3.T q) := penumPt_canon (a3_spec.1 q hq)

theorem r3_canon {q : Nat} (hq : q < R3A.cnt) : Cn (R3A.T q) := penumPt_canon (r3_spec.1 q hq)

theorem a3_sort : ∀ i < A3.cnt, r32 A3.SRT i < A3.cnt ∧ r32 A3.SRI (r32 A3.SRT i) = i ∧
    (i + 1 < A3.cnt → A3.T (r32 A3.SRT i) < A3.T (r32 A3.SRT (i + 1))) :=
  fun i hi => (penumPt_specH (a3_spec.1 i hi)).2.2.2

theorem r3_sort : ∀ i < R3A.cnt, r32 R3A.SRT i < R3A.cnt ∧ r32 R3A.SRI (r32 R3A.SRT i) = i ∧
    (i + 1 < R3A.cnt → R3A.T (r32 R3A.SRT i) < R3A.T (r32 R3A.SRT (i + 1))) :=
  fun i hi => (penumPt_specH (r3_spec.1 i hi)).2.2.2

theorem enumA3_eq : enumA3 = hRec 275 9 A3.cnt A3.T A3.PL :=
  (mulH_sound (k := 4) hn (fun j hj => (fa.1 j hj).1) tabs_ag fa.2.1 a3_spec.1 a3_spec.2).1

theorem enumClass_eq : enumClass = hRec 275 9 R3A.cnt R3A.T R3A.PL := by
  have h := conjH_sound (k := 2) (X := TT.F 0) hn tabs_pg tabs_pgi (tabTT (by norm_num))
    (by rw [← fa.2.2.2.2.1]; exact fa.2.2.2.2.2.1) r3_spec.1 r3_spec.2
  exact h.1

theorem memT_at {cnt : Nat} {T PL POS : Nat → Nat} {i X : Nat} (hX : Cn X)
    (h : atK cnt T POS i X = true) : memT 275 (hRec 275 9 cnt T PL).1 (tabT (unpack 275 9 X)) = true := by
  unfold atK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hT : T (r32 POS i) = X := Nat.eq_of_beq_eq_true h2
  exact memT_of (T := T) (Nat.le_of_ble_eq_true h1) (by rw [hT]; exact tblEq_self hX)

theorem tab_at {cnt q : Nat} {T PL : Nat → Nat} (hq : q < cnt) :
    (hRec 275 9 cnt T PL).1[q]! = tabT (unpack 275 9 (T q)) := hRec_get hq

theorem nrmY_ok : (tblEq 275 nrmY[0]! (threeTbl 0) && nrmY.all (fun y => permOK 275 y &&
      invOK 275 y (invT 275 y) && memT 275 enumA3.1 y && memT 275 enumClass.1 y)) = true := by
  rw [Bool.and_eq_true, nrmY_get (by norm_num), tabTT (by norm_num), fc.2.1,
    tblEq_unpack (TTc (by norm_num)) (TTc (by norm_num)), Nat.beq_refl]
  refine ⟨rfl, all_of_get nrmY_size (fun k hk => nrmY_get hk) fun j hj => ?_⟩
  rw [invT_unpack (by norm_num) (NTinv (by omega)), enumA3_eq, enumClass_eq]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨permOK_unpack (NTc (by omega)) (NTinv (by omega)),
    invOK_unpack (NTc (by omega)) (NTIc (by omega)) (NTinv (by omega))⟩,
    memT_at (NTc (by omega)) (fc.1 j hj).2⟩, memT_at (NTc (by omega)) (fc.1 j hj).1⟩

theorem nrmY_pairs : (List.range 10).all (fun i => (List.range 10).all fun j =>
    i == j || (!tblEq 275 nrmY[i]! nrmY[j]! && !tblEq 275 nrmY[i]! (invT 275 nrmY[j]!))) = true := by
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  by_cases e : i = j
  · rw [e, beq_self_eq_true, Bool.true_or]
  · obtain ⟨n1, n2⟩ := fc.2.2.1 i hi' j hj' e
    rw [nrmY_get hi', nrmY_get hj', invT_unpack (by norm_num) (NTinv (by omega)),
      tblEq_unpack (NTc (by omega)) (NTc (by omega)), tblEq_unpack (NTc (by omega)) (NTIc (by omega)),
      Bool.eq_false_iff.2 fun h => n1 (Nat.eq_of_beq_eq_true h),
      Bool.eq_false_iff.2 fun h => n2 (Nat.eq_of_beq_eq_true h)]
    simp

theorem enumA3_ok : enumA3.1.all (fun z => !memT 275 enumClass.1 z ||
    nrmY.any fun y => tblEq 275 z y || tblEq 275 z (invT 275 y)) = true := by
  rw [enumA3_eq, enumClass_eq]
  refine all_hRec fun q hq => ?_
  have hz := slK_spec fc.2.2.2.1 q (Nat.zero_le _) (by
    have := fa.2.1
    unfold penumHdK at this
    simp only [bAnd_iff, Nat.ble_eq] at this
    omega) hq
  have hc := a3_canon hq
  unfold zK at hz
  rw [PEnum.strictB_app'] at hz
  cases e : atK R3A.cnt R3A.T AIn3A q (A3.T q) with
  | true =>
    rw [e] at hz
    change anyYK NT.F NTI (A3.T q) = true at hz
    have hany : ∃ j < 10, yPredK NT.F NTI (A3.T q) j = true := by
      by_contra hne
      have hne' : ∀ j < 10, yPredK NT.F NTI (A3.T q) j = false := fun j hj =>
        Bool.eq_false_iff.2 fun hp => hne ⟨j, hj, hp⟩
      have ha : allN 10 (fun j => bIf(yPredK NT.F NTI (A3.T q) j, false, true)) = true :=
        allN_of fun j hj => by rw [hne' j hj]
      unfold anyYK at hz
      rw [ha] at hz
      exact absurd hz (by decide)
    obtain ⟨j, hj, hp⟩ := hany
    rw [any_of_get nrmY_size (fun k hk => nrmY_get hk) hj (p := fun y =>
      tblEq 275 (tabT (unpack 275 9 (A3.T q))) y || tblEq 275 (tabT (unpack 275 9 (A3.T q)))
        (invT 275 y)) (by rw [← nrmY_get hj, yPred_eq hc hj]; exact hp)]
    simp
  | false =>
    rw [e] at hz
    change brK R3A.cnt R3A.T R3A.SRT (A3.T q) (r32 BrA q) = true at hz
    rw [not_memT_of r3_sort (fun q hq => r3_canon hq) hc hz]
    rfl

theorem nrmYCheck_true : nrmYCheck = true := by
  unfold nrmYCheck
  have hs : (nrmY.size == 10) = true := by rw [nrmY_size]; rfl
  have h1 := nrmY_ok
  rw [Bool.and_eq_true] at h1
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨hs, h1.1⟩, h1.2⟩, nrmY_pairs⟩, enumA3_ok⟩

theorem cj_canon {g gi x : Nat} (hg : Cn g) (hgi : Cn gi) (hx : Cn x) : Cn (cj g gi x) :=
  canonK_pcomp (canonK_pcomp hg hx) hgi

theorem conjT_eq {g gi x : Nat} (hg : Cn g) (hgi : Cn gi) (hx : Cn x) :
    conjT 275 (tabT (unpack 275 9 g)) (tabT (unpack 275 9 gi)) (tabT (unpack 275 9 x)) =
      tabT (unpack 275 9 (cj g gi x)) := conjT_unpack hg hgi hx

theorem nrmNormCheck_true : nrmNormCheck = true := by
  unfold nrmNormCheck
  have hs : (nrmN.size == 2) = true := rfl
  simp only [Bool.and_eq_true]
  refine ⟨⟨hs, all_of_get (m := 2) rfl (fun k hk => nrmN_get hk) fun k hk => ?_⟩,
    all_of_get (m := 2) rfl (fun k hk => nrmN_get hk) fun k hk => ?_⟩
  · have hN := NTc (k := 10 + k) (by omega)
    have hNI := NTIc (k := 10 + k) (by omega)
    have hinv := NTinv (k := 10 + k) (by omega)
    rw [invT_unpack (by norm_num) hinv, sift_eq hN]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨permOK_unpack hN hinv, (fc.2.2.2.2.1 k hk).1⟩, invOK_unpack hN hNI hinv⟩,
      all_of_get aGens3_size (fun l hl => aGens3_get hl) fun l hl => ?_⟩
    rw [conjT_eq hN hNI (TLc (by omega)), enumA3_eq]
    exact memT_at (cj_canon hN hNI (TLc (by omega))) ((fc.2.2.2.2.1 k hk).2.1 l hl)
  · have hN := NTc (k := 10 + k) (by omega)
    have hNI := NTIc (k := 10 + k) (by omega)
    have hinv := NTinv (k := 10 + k) (by omega)
    rw [invT_unpack (by norm_num) hinv]
    refine all_of_get nrmY_size (fun i hi => nrmY_get hi) fun i hi => ?_
    rw [conjT_eq hN hNI (NTc (by omega)), decide_eq_true_iff]
    exact nrmPt_lt (cj_canon hN hNI (NTc (by omega))) ((fc.2.2.2.2.1 k hk).2.2 i hi)

theorem nrmAct_of {N NI W : Nat} (hN : Cn N) (hNI : Cn NI)
    (hinv : invEqK 275 9 (mask 9) (275 * 9) N NI = true)
    (hW : ∀ i < 10, firstK NT.F NTI (cj N NI (NT.F i)) (pg 4 (mask 4) W i) = true) :
    nrmAct (tabT (unpack 275 9 N)) = tabT (unpack 10 4 W) := by
  have hI : invT 275 (tabT (unpack 275 9 N)) = tabT (unpack 275 9 NI) :=
    invT_unpack (n := 275) (by norm_num) hinv
  have hpt : ∀ i < 10, nrmPt (conjT 275 (tabT (unpack 275 9 N)) (invT 275 (tabT (unpack 275 9 N)))
      nrmY[i]!) = pg 4 (mask 4) W i := fun i hi => by
    rw [hI, nrmY_get hi, conjT_eq hN hNI (NTc (by omega))]
    exact nrmPt_eq (cj_canon hN hNI (NTc (by omega))) (hW i hi)
  unfold nrmAct
  have hsz : (tabT (unpack 10 4 W)).size = 10 := by
    simp only [tabT, Array.size_map, unpack, Array.size_ofFn]
  apply Array.ext
  · rw [hsz, Array.size_ofFn]
  · intro i h1 h2
    have hi : i < 10 := by simpa using h1
    rw [Array.getElem_ofFn, ← getElem!_pos _ i h2, tabT_get, CFSG.KS.Raw.Orb.unpack_get hi]
    exact congrArg UInt32.ofNat (hpt i hi)

theorem nrmAct_eq {k : Nat} (hk : k < 2) :
    nrmAct (tabT (unpack 275 9 (NT.F (10 + k)))) = tabT (unpack 10 4 (NW.GI k)) :=
  nrmAct_of (NTc (by omega)) (NTIc (by omega)) (NTinv (by omega)) (fb.2.2.2.2.2.2.1 k hk)

theorem nrmW_get {k : Nat} (hk : k < 2) : nrmW[k]! = tabT (unpack 10 4 (NW.GI k)) := by
  unfold nrmW
  have hk' : k < nrmN.size := hk
  rw [getElem!_pos _ k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
    ← getElem!_pos nrmN k hk', nrmN_get hk, nrmAct_eq hk]

theorem tabs_nw : TabsOK 10 4 2 NW.GI nrmW :=
  ⟨by simp [nrmW, nrmN], fun j hj => ⟨nrmW_get hj, (fb.2.1 j hj).2.1⟩⟩

theorem nrmClosure_eq : nrmClosure = hRec 10 4 NW.cnt NW.T NW.PL ∧
    mulTreeOK 10 nrmW (hRec 10 4 NW.cnt NW.T NW.PL).1 (hRec 10 4 NW.cnt NW.T NW.PL).2.1
      (hRec 10 4 NW.cnt NW.T NW.PL).2.2 = true := by
  have h := mulH_sound (n := 10) (w := 4) (k := 2) fb.1 (fun j hj => (fb.2.1 j hj).1) tabs_nw
    fb.2.2.1 nw_spec.1 nw_spec.2
  exact ⟨h.1, h.2.1⟩

theorem trip_of {a b c : Nat} (ha : a < 10) (hb : b < 10) (hc : c < 10) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : ∃ q < NW.cnt, pg 4 (mask 4) (NW.T q) 0 = a ∧
      pg 4 (mask 4) (NW.T q) 1 = b ∧ pg 4 (mask 4) (NW.T q) 2 = c := by
  have h := fb.2.2.2.2.2.2.2 (100 * a + 10 * b + c) (by omega)
  unfold tripK at h
  have e1 : Nat.div (100 * a + 10 * b + c) 100 = a := by
    change (100 * a + 10 * b + c) / 100 = a
    omega
  have e2 : Nat.mod (Nat.div (100 * a + 10 * b + c) 10) 10 = b := by
    change (100 * a + 10 * b + c) / 10 % 10 = b
    omega
  have e3 : Nat.mod (100 * a + 10 * b + c) 10 = c := by
    change (100 * a + 10 * b + c) % 10 = c
    omega
  have hlt : Nat.blt (100 * a + 10 * b + c) 1000 = true := Nat.blt_eq.mpr (by omega)
  rw [e1, e2, e3, hlt, Bool.eq_false_iff.2 (fun h => hab (Nat.eq_of_beq_eq_true h)),
    Bool.eq_false_iff.2 (fun h => hac (Nat.eq_of_beq_eq_true h)),
    Bool.eq_false_iff.2 (fun h => hbc (Nat.eq_of_beq_eq_true h))] at h
  have h' : strictB (r32 Trip (100 * a + 10 * b + c)) (fun q => bAnd(Nat.blt q NW.cnt,
      bAnd(Nat.beq (pg 4 (mask 4) (NW.T q) 0) a, bAnd(Nat.beq (pg 4 (mask 4) (NW.T q) 1) b,
        Nat.beq (pg 4 (mask 4) (NW.T q) 2) c)))) = true := h
  rw [PEnum.strictB_app'] at h'
  simp only [bAnd_iff, Nat.beq_eq] at h'
  exact ⟨_, Nat.blt_eq.mp h'.1, h'.2⟩

theorem nrmTransCheck_true : nrmTransCheck = true := by
  unfold nrmTransCheck
  obtain ⟨e, htree⟩ := nrmClosure_eq
  rw [e]
  simp only [Bool.and_eq_true]
  refine ⟨⟨all_of_get (m := 2) (by simp [nrmW, nrmN]) (fun k hk => nrmW_get hk) fun k hk =>
    permOK_unpack (fb.2.1 k hk).2.1 (fb.2.1 k hk).2.2.2, htree⟩, ?_⟩
  simp only [List.all_eq_true, List.mem_range]
  intro a ha b hb c hc
  by_cases hab : a = b
  · simp [hab]
  by_cases hac : a = c
  · simp [hac]
  by_cases hbc : b = c
  · simp [hbc]
  obtain ⟨q, hq, h0, h1, h2⟩ := trip_of ha hb hc hab hac hbc
  have hcq : canonK 10 4 (mask 4) (10 * 4) (NW.T q) = true := penumPt_canon (nw_spec.1 q hq)
  have hany : (hRec 10 4 NW.cnt NW.T NW.PL).1.any (fun e => ap e 0 == a && ap e 1 == b &&
      ap e 2 == c) = true := by
    refine any_of_get (hRec_size 10 4 NW.cnt NW.T NW.PL) (fun k hk => hRec_get hk) hq ?_
    rw [ap_tabT _ (unpack_lt hcq), ap_tabT _ (unpack_lt hcq), ap_tabT _ (unpack_lt hcq),
      CFSG.KS.Raw.Orb.unpack_get (by norm_num), CFSG.KS.Raw.Orb.unpack_get (by norm_num),
      CFSG.KS.Raw.Orb.unpack_get (by norm_num), h0, h1, h2]
    simp
  rw [hany]
  simp

theorem cImg_canon {i j l : Nat} (hi : i < 10) (hj : j < 10) (hl : l < 4) : Cn (cImg i j l) :=
  cj_canon (NTIc (by omega)) (NTc (by omega)) (cj_canon (NTc (by omega)) (NTIc (by omega))
    (TLc (by omega)))

theorem cw_of {i j : Nat} (hi : i < 10) (hj : j < 10) (hij : i ≠ j) :
    ∃ l < 4, ∃ s, brK A3.cnt A3.T A3.SRT (cImg i j l) s = true := by
  have h := fc.2.2.2.2.2.2 (10 * i + j) (by omega)
  unfold cwK at h
  have e1 : Nat.div (10 * i + j) 10 = i := by
    change (10 * i + j) / 10 = i
    omega
  have e2 : Nat.mod (10 * i + j) 10 = j := by
    change (10 * i + j) % 10 = j
    omega
  rw [e1, e2, Bool.eq_false_iff.2 (fun h => hij (Nat.eq_of_beq_eq_true h))] at h
  have h' : strictB (r32 CW (10 * i + j)) (fun w => bAnd(Nat.blt (Nat.mod w 4) 4,
      brK A3.cnt A3.T A3.SRT (cImg i j (Nat.mod w 4)) (Nat.div w 4))) = true := h
  rw [PEnum.strictB_app'] at h'
  obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 h'
  exact ⟨_, Nat.blt_eq.mp a1, _, a2⟩

theorem nrmConjCheck_true : nrmConjCheck = true := by
  unfold nrmConjCheck
  have hs : (nrmC.size == 10) = true := by rw [nrmC_size]; rfl
  simp only [Bool.and_eq_true]
  refine ⟨⟨hs, all_of_get nrmC_size (fun k hk => nrmC_get hk) fun k hk => ?_⟩, ?_⟩
  · have hC := NTc (k := 12 + k) (by omega)
    have hCI := NTIc (k := 12 + k) (by omega)
    have hinv := NTinv (k := 12 + k) (by omega)
    have hT := TTc (k := 0) (by norm_num)
    have hcm : pcomp 275 9 (mask 9) (NT.F (12 + k)) (TT.F 0) =
        pcomp 275 9 (mask 9) (TT.F 0) (NT.F (12 + k)) := (fc.2.2.2.2.2.1 k hk).2
    rw [invT_unpack (by norm_num) hinv, sift_eq hC, tabTT (by norm_num), commTT_unpack hC hT, hcm]
    simp only [Bool.and_eq_true, Nat.beq_refl, and_true]
    exact ⟨⟨permOK_unpack hC hinv, (fc.2.2.2.2.2.1 k hk).1⟩, invOK_unpack hC hCI hinv⟩
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi j hj
    by_cases hij : i = j
    · simp [hij]
    obtain ⟨l, hl, s, hb⟩ := cw_of hi hj hij
    have hany : aGens3.any (fun a => !memT 275 enumA3.1 (conjT 275 (invT 275 nrmC[j]!) nrmC[j]!
        (conjT 275 nrmC[i]! (invT 275 nrmC[i]!) a))) = true := by
      refine any_of_get aGens3_size (fun k hk => aGens3_get hk) hl ?_
      rw [nrmC_get hi, nrmC_get hj, invT_unpack (by norm_num) (NTinv (by omega)),
        invT_unpack (by norm_num) (NTinv (by omega)),
        conjT_eq (NTc (by omega)) (NTIc (by omega)) (TLc (by omega)),
        conjT_eq (NTIc (by omega)) (NTc (by omega))
          (cj_canon (NTc (by omega)) (NTIc (by omega)) (TLc (by omega))), enumA3_eq]
      have hm := not_memT_of (PL := A3.PL) a3_sort (fun q hq => a3_canon hq)
        (cImg_canon hi hj hl) hb
      unfold cImg at hm
      rw [hm]
      rfl
    rw [hany]
    simp

theorem nrmCheck_true : nrmCheck = true := by
  unfold nrmCheck
  rw [nrmYCheck_true, nrmNormCheck_true, nrmTransCheck_true, nrmConjCheck_true]
  rfl

end CertificateChecks.KernelMcLAS

end
