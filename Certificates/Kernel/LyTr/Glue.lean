module

public import Certificates.Kernel.LyTr.Checks243
public import Certificates.Kernel.LyTr.ChecksR1
public import Certificates.Kernel.LyTr.ChecksR1A
public import Certificates.Kernel.LyTr.ChecksR1B
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.MulHFSound
public import CFSG.Certificates.Kernel.BfsPinAlg
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.LyonsSims

abbrev C8 (p : Nat) : Prop := canonK 243 8 (mask 8) (243 * 8) p = true

abbrev C11 (p : Nat) : Prop := canonK 1080 11 (mask 11) (1080 * 11) p = true

theorem split3 {a b c : Bool} (h : bAnd(a, bAnd(b, c)) = true) : a = true ∧ b = true ∧ c = true := by
  simp only [bAnd_iff] at h
  exact h

theorem base8 : szOK 243 8 = true ∧ C8 id8 ∧ CFSG.KS.Prim.idK 243 8 (mask 8) = true ∧
    (∀ j < 5, C8 (GH.F j) ∧ C8 (GHI j) ∧ i8 (GH.F j) (GHI j) = true) ∧
    (∀ j < 3, C8 (LH.F j) ∧ C8 (LHI j) ∧ i8 (LH.F j) (LHI j) = true) ∧
    (∀ j < 5, C8 (R2.GI j) ∧ C8 (R2I j) ∧ i8 (R2.GI j) (R2I j) = true ∧ R2.G j = id8) ∧
    (∀ j < 6, C8 (RP j) ∧ C8 (RPI j) ∧ i8 (RP j) (RPI j) = true) ∧
    R2.cnt = 3888 ∧ penumHdK id8 R2.cnt 5000 R2.T R2.PL = true := by
  have h := k_base
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨a1, a2, a3, fun j hj => split3 (allN_spec a4 j hj), fun j hj => split3 (allN_spec a5 j hj),
    fun j hj => ?_, fun j hj => split3 (allN_spec a7 j hj), Nat.eq_of_beq_eq_true a8, a9⟩
  have e := allN_spec a6 j hj
  simp only [bAnd_iff] at e
  exact ⟨e.1, e.2.1, e.2.2.1, Nat.eq_of_beq_eq_true e.2.2.2⟩

theorem base11 : szOK 1080 11 = true ∧ C11 id11 ∧ CFSG.KS.Prim.idK 1080 11 (mask 11) = true ∧
    (∀ j < 4, C11 (UH.F j) ∧ C11 (UHI j) ∧ i11 (UH.F j) (UHI j) = true) ∧
    (∀ j < 5, C11 (R1.GI j) ∧ R1.G j = id11 ∧
      wK 1080 11 LU (Ly1080.txyWords.getD j []) = R1.GI j) ∧
    R1.cnt = 3888 ∧ penumHdK id11 R1.cnt 5000 R1.T R1.PL = true := by
  have h := k_r1base
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨a1, a2, a3, fun j hj => split3 (allN_spec a4 j hj), fun j hj => ?_,
    Nat.eq_of_beq_eq_true a6, a7⟩
  have e := allN_spec a5 j hj
  simp only [bAnd_iff] at e
  exact ⟨e.1, Nat.eq_of_beq_eq_true e.2.1, Nat.eq_of_beq_eq_true e.2.2⟩

theorem hid8 : idT 243 = tabT (unpack 243 8 id8) := by
  rw [idT_tabT, ← idK_sound base8.2.2.1]
  rfl

theorem hid11 : idT 1080 = tabT (unpack 1080 11 id11) := by
  rw [idT_tabT, ← idK_sound base11.2.2.1]
  rfl

theorem tab_of_nat {x : Table} {u : Array Nat} (h : natArr x = u) : x = tabT u := by
  rw [← h, tabT_natArr]

theorem get_map {a : Array Table} {f : Table → Table} {j : Nat} (hj : j < a.size) :
    (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj, Array.getElem_map]

theorem map_eq_compT' {n : Nat} {P T : Table} (hT : T.size = n) :
    T.map (fun t => P[t.toNat]!) = compT n P T := by
  apply Array.ext (by simp [compT, hT])
  intro i h1 h2
  simp only [Array.getElem_map, compT, Array.getElem_ofFn]
  rw [getElem!_pos T i (by simpa using h1)]

theorem wordT_eqK {n w : Nat} (hid : idT n = tabT (unpack n w (pidn n w)))
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true) {gens : Int → Table} {G : Int → Nat} :
    ∀ wd : List Int, (∀ l ∈ wd, gens l = tabT (unpack n w (G l)) ∧
      canonK n w (mask w) (n * w) (G l) = true) →
      wordT n gens wd = tabT (unpack n w (wK n w G wd)) ∧
        canonK n w (mask w) (n * w) (wK n w G wd) = true
  | [], _ => ⟨hid, hidc⟩
  | l :: wd, h => by
    obtain ⟨ih1, ih2⟩ := wordT_eqK hid hidc wd fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    obtain ⟨g1, g2⟩ := h l List.mem_cons_self
    have e : wordT n gens (l :: wd) = (wordT n gens wd).map (fun t => (gens l)[t.toNat]!) := rfl
    rw [e, ih1, g1, map_eq_compT' (n := n) (by simp [tabT, unpack]), compT_unpack g2 ih2]
    exact ⟨rfl, canonK_pcomp g2 ih2⟩

theorem genT {j : Nat} (hj : j < 5) : Ly243.genTabs[j]! = tabT (unpack 243 8 (GH.F j)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound GH.all (by norm_num) j hj
  rw [← GH.eq] at h
  rw [getElem!_pos _ j (by simp [Ly243.genTabs]; omega)]
  simp only [Ly243.genTabs, Array.getElem_ofFn]
  exact tab_of_nat h

theorem genIT {j : Nat} (hj : j < 5) : Ly243.genInvTabs[j]! = tabT (unpack 243 8 (GHI j)) := by
  unfold Ly243.genInvTabs
  rw [get_map (by simp [Ly243.genTabs]; omega), genT hj,
    invT_unpack (by norm_num) (base8.2.2.2.1 j hj).2.2]

theorem lineT {j : Nat} (hj : j < 3) : Ly243.lineTabs[j]! = tabT (unpack 243 8 (LH.F j)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound LH.all (by norm_num) j hj
  rw [← LH.eq] at h
  rw [getElem!_pos _ j (by simp [Ly243.lineTabs]; omega)]
  simp only [Ly243.lineTabs, Array.getElem_ofFn]
  exact tab_of_nat h

theorem lineIT {j : Nat} (hj : j < 3) : Ly243.lineInvTabs[j]! = tabT (unpack 243 8 (LHI j)) := by
  unfold Ly243.lineInvTabs
  rw [get_map (by simp [Ly243.lineTabs]; omega), lineT hj,
    invT_unpack (by norm_num) (base8.2.2.2.2.1 j hj).2.2]

theorem trLetT {l : Int} (h0 : l ≠ 0) (h5 : l.natAbs ≤ 5) :
    Ly243.trLet l = tabT (unpack 243 8 (LG l)) ∧ C8 (LG l) := by
  unfold Ly243.trLet LG
  by_cases hl : 0 < l
  · simp only [hl, ↓reduceIte]
    have hj : l.toNat - 1 < 5 := by omega
    exact ⟨genT hj, (base8.2.2.2.1 _ hj).1⟩
  · simp only [hl, ↓reduceIte]
    have hj : (-l).toNat - 1 < 5 := by omega
    exact ⟨genIT hj, (base8.2.2.2.1 _ hj).2.1⟩

theorem txyWords_ok : ∀ j < 5, ∀ l ∈ Ly243.txyWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 5 := by
  decide

theorem repWords_ok : ∀ j < 6, ∀ l ∈ Ly243.repWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 5 := by
  decide

theorem kw : (∀ j < 5, wK 243 8 LG (Ly243.txyWords.getD j []) = R2.GI j) ∧
    (∀ j < 6, wK 243 8 LG (Ly243.repWords.getD j []) = RP j) := by
  have h := k_words
  simp only [bAnd_iff] at h
  exact ⟨fun j hj => Nat.eq_of_beq_eq_true (allN_spec h.1 j hj),
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec h.2 j hj)⟩

theorem txy243T {j : Nat} (hj : j < 5) : Ly243.txyTabs[j]! = tabT (unpack 243 8 (R2.GI j)) := by
  have hs : Ly243.txyWords.length = 5 := by decide
  unfold Ly243.txyTabs
  rw [getElem!_pos _ j (by simp [hs, hj]), Array.getElem_map]
  have e : Ly243.txyWords.toArray[j]'(by simp [hs, hj]) = Ly243.txyWords.getD j [] := by
    simp [List.getD_eq_getElem?_getD, hs, hj]
  rw [e, (wordT_eqK hid8 base8.2.1 _ fun l hl =>
    trLetT (txyWords_ok j hj l hl).1 (txyWords_ok j hj l hl).2).1, kw.1 j hj]

theorem txy243IT {j : Nat} (hj : j < 5) :
    Ly243.txyInvTabs[j]! = tabT (unpack 243 8 (R2I j)) := by
  have hs : Ly243.txyWords.length = 5 := by decide
  unfold Ly243.txyInvTabs
  rw [get_map (by simp [Ly243.txyTabs, hs]; omega), txy243T hj,
    invT_unpack (by norm_num) (base8.2.2.2.2.2.1 j hj).2.2.1]

theorem repT {j : Nat} (hj : j < 6) : Ly243.repTabs[j]! = tabT (unpack 243 8 (RP j)) := by
  have hs : Ly243.repWords.length = 6 := by decide
  unfold Ly243.repTabs
  rw [getElem!_pos _ j (by simp [hs, hj]), Array.getElem_map]
  have e : Ly243.repWords.toArray[j]'(by simp [hs, hj]) = Ly243.repWords.getD j [] := by
    simp [List.getD_eq_getElem?_getD, hs, hj]
  rw [e, (wordT_eqK hid8 base8.2.1 _ fun l hl =>
    trLetT (repWords_ok j hj l hl).1 (repWords_ok j hj l hl).2).1, kw.2 j hj]

theorem txyLetT {l : Int} (h0 : l ≠ 0) (h5 : l.natAbs ≤ 5) :
    Ly243.txyLet l = tabT (unpack 243 8 (LT l)) ∧ C8 (LT l) := by
  unfold Ly243.txyLet LT
  by_cases hl : 0 < l
  · simp only [hl, ↓reduceIte]
    have hj : l.toNat - 1 < 5 := by omega
    exact ⟨txy243T hj, (base8.2.2.2.2.2.1 _ hj).1⟩
  · simp only [hl, ↓reduceIte]
    have hj : (-l).toNat - 1 < 5 := by omega
    exact ⟨txy243IT hj, (base8.2.2.2.2.2.1 _ hj).2.1⟩

theorem uT {j : Nat} (hj : j < 4) : Ly1080.uTabs[j]! = tabT (unpack 1080 11 (UH.F j)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound UH.all (by norm_num) j hj
  rw [← UH.eq] at h
  rw [getElem!_pos _ j (by simp [Ly1080.uTabs]; omega)]
  simp only [Ly1080.uTabs, Array.getElem_ofFn]
  exact tab_of_nat h

theorem uIT {j : Nat} (hj : j < 4) : Ly1080.uInvTabs[j]! = tabT (unpack 1080 11 (UHI j)) := by
  unfold Ly1080.uInvTabs
  rw [get_map (by simp [Ly1080.uTabs]; omega), uT hj,
    invT_unpack (by norm_num) (base11.2.2.2.1 j hj).2.2]

theorem uLetT {l : Int} (h0 : l ≠ 0) (h4 : l.natAbs ≤ 4) :
    Ly1080.uLet l = tabT (unpack 1080 11 (LU l)) ∧ C11 (LU l) := by
  unfold Ly1080.uLet LU
  by_cases hl : 0 < l
  · simp only [hl, ↓reduceIte]
    have hj : l.toNat - 1 < 4 := by omega
    exact ⟨uT hj, (base11.2.2.2.1 _ hj).1⟩
  · simp only [hl, ↓reduceIte]
    have hj : (-l).toNat - 1 < 4 := by omega
    exact ⟨uIT hj, (base11.2.2.2.1 _ hj).2.1⟩

theorem txy1080Words_ok : ∀ j < 5, ∀ l ∈ Ly1080.txyWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 4 := by
  decide

theorem txy1080T {j : Nat} (hj : j < 5) :
    Ly1080.txyTabs[j]! = tabT (unpack 1080 11 (R1.GI j)) := by
  have hs : Ly1080.txyWords.length = 5 := by decide
  unfold Ly1080.txyTabs
  rw [getElem!_pos _ j (by simp [hs, hj]), Array.getElem_map]
  have e : Ly1080.txyWords.toArray[j]'(by simp [hs, hj]) = Ly1080.txyWords.getD j [] := by
    simp [List.getD_eq_getElem?_getD, hs, hj]
  rw [e, (wordT_eqK hid11 base11.2.1 _ fun l hl =>
    uLetT (txy1080Words_ok j hj l hl).1 (txy1080Words_ok j hj l hl).2).1,
    (base11.2.2.2.2.1 j hj).2.2]

theorem r2Sl_all : ∀ s < 16, r2Sl s = true := by
  intro s hs
  interval_cases s
  exacts [k_r2s0, k_r2s1, k_r2s2, k_r2s3, k_r2s4, k_r2s5, k_r2s6, k_r2s7, k_r2s8, k_r2s9, k_r2s10,
    k_r2s11, k_r2s12, k_r2s13, k_r2s14, k_r2s15]

theorem r2_pe : ∀ i < R2.cnt, penumPtK 243 8 (mask 8) (243 * 8) true R2.G R2.GI 5 R2.cnt
    R2.T R2.PL R2.POS R2.SRT R2.SRI i = true := by
  intro i hi
  have hc : R2.cnt = 3888 := base8.2.2.2.2.2.2.2.1
  have hs := r2Sl_all (i / 243) (by omega)
  exact penumSl_spec hs i (by omega) (by omega) hi

theorem r2_hs : ∀ i < R2.cnt, hsortPtK 243 8 (mask 8) R2.cnt R2.T R2.HS R2.HSI i = true :=
  fun i hi => by
    rw [← hsortPtKF_eq 243 8 R2.cnt R2.T R2.HS R2.HSI i]
    exact slK_spec k_r2h i (Nat.zero_le _) (by omega) hi

theorem slices8 {P : Nat → Prop} (h : ∀ s < 8, ∀ i, 486 * s ≤ i → i < 486 * s + 486 → P i) :
    ∀ i < 3888, P i := fun i hi => h (i / 486) (by omega) i (by omega) (by omega)

theorem r1Sl_all : ∀ s < 48, r1Sl s = true := by
  intro s hs
  interval_cases s
  exacts [k_r1s0, k_r1s1, k_r1s2, k_r1s3, k_r1s4, k_r1s5, k_r1s6, k_r1s7, k_r1s8, k_r1s9, k_r1s10,
    k_r1s11, k_r1s12, k_r1s13, k_r1s14, k_r1s15, k_r1s16, k_r1s17, k_r1s18, k_r1s19, k_r1s20,
    k_r1s21, k_r1s22, k_r1s23, k_r1s24, k_r1s25, k_r1s26, k_r1s27, k_r1s28, k_r1s29, k_r1s30,
    k_r1s31, k_r1s32, k_r1s33, k_r1s34, k_r1s35, k_r1s36, k_r1s37, k_r1s38, k_r1s39, k_r1s40,
    k_r1s41, k_r1s42, k_r1s43, k_r1s44, k_r1s45, k_r1s46, k_r1s47]

theorem r1_pe : ∀ i < R1.cnt, penumPtK 1080 11 (mask 11) (1080 * 11) true R1.G R1.GI 5 R1.cnt
    R1.T R1.PL R1.POS R1.SRT R1.SRI i = true := by
  intro i hi
  have hc : R1.cnt = 3888 := base11.2.2.2.2.2.1
  have hs := r1Sl_all (i / 81) (by omega)
  exact penumSl_spec hs i (by omega) (by omega) hi

theorem r1_hsF : ∀ i < R1.cnt, hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI i = true := by
  have hc := base11.2.2.2.2.2.1
  rw [hc]
  refine slices8 fun s hs i h1 h2 => ?_
  interval_cases s
  · exact slK_spec k_r1h0 i (by omega) (by omega) (by omega)
  · exact slK_spec k_r1h1 i (by omega) (by omega) (by omega)
  · exact slK_spec k_r1h2 i (by omega) (by omega) (by omega)
  · exact slK_spec k_r1h3 i (by omega) (by omega) (by omega)
  · exact slK_spec k_r1h4 i (by omega) (by omega) (by omega)
  · exact slK_spec k_r1h5 i (by omega) (by omega) (by omega)
  · exact slK_spec k_r1h6 i (by omega) (by omega) (by omega)
  · exact slK_spec k_r1h7 i (by omega) (by omega) (by omega)

theorem r1_hs : ∀ i < R1.cnt, hsortPtK 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI i = true :=
  fun i hi => by
    rw [← hsortPtKF_eq 1080 11 R1.cnt R1.T R1.HS R1.HSI i]
    exact r1_hsF i hi

end CertificateChecks.KernelLyTr

end
