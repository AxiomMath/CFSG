module

public import Certificates.Kernel.Sporadic.OddCore.McLKl
public import Certificates.Kernel.Sporadic.OddCore.McLTwoF
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLKl

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CertificateChecks.KernelCensus

theorem base : szOK 275 9 = true ∧ canonK 275 9 (mask 9) (275 * 9) (pidn 275 9) = true ∧
    CFSG.KS.Prim.idK 275 9 (mask 9) = true ∧
    allN 3 (fun j => bAnd(cK (McLKlH.F j), bAnd(Nat.beq (McLKlS.GI j) (McLKlH.F j),
      bAnd(Nat.beq (McLKlS.G j) (pidn 275 9), bAnd(cK (McLKlSI j),
        invEqK 275 9 (mask 9) (275 * 9) (McLKlH.F j) (McLKlSI j)))))) = true ∧
    McLKlS.cnt = 8 ∧ penumHdK (pidn 275 9) McLKlS.cnt 200 McLKlS.T McLKlS.PL = true := by
  have h := base_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨a1, a2, a3, a4, Nat.eq_of_beq_eq_true a5, a6⟩

theorem gen {j : Nat} (hj : j < 3) : canonK 275 9 (mask 9) (275 * 9) (McLKlH.F j) = true ∧
    McLKlS.GI j = McLKlH.F j ∧ McLKlS.G j = pidn 275 9 ∧
    canonK 275 9 (mask 9) (275 * 9) (McLKlSI j) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLKlH.F j) (McLKlSI j) = true := by
  have h := allN_spec base.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  exact ⟨a1, Nat.eq_of_beq_eq_true a2, Nat.eq_of_beq_eq_true a3, a4, a5⟩

theorem tab {j : Nat} (hj : j < 3) : sylAGens[j]! = tabT (unpack 275 9 (McLKlH.F j)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound McLKlH.all (by norm_num) j hj
  rw [← McLKlH.eq] at h
  unfold sylAGens
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change sylATbl j = _
  unfold sylATbl
  rw [← h, tabT_natArr]

theorem s_tabs : TabsOK 275 9 3 McLKlS.GI sylAGens := by
  refine ⟨by simp [sylAGens], fun j hj => ?_⟩
  rw [(gen hj).2.1]
  exact ⟨tab hj, (gen hj).1⟩

theorem s_invs : ∀ j < 3, invEqK 275 9 (mask 9) (275 * 9) (McLKlS.GI j) (McLKlSI j) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (McLKlSI j) = true := fun j hj => by
  rw [(gen hj).2.1]
  exact ⟨(gen hj).2.2.2.2, (gen hj).2.2.2.1⟩

theorem s_pe : ∀ i < McLKlS.cnt, penumPtK 275 9 (mask 9) (275 * 9) true McLKlS.G McLKlS.GI 3
    McLKlS.cnt McLKlS.T McLKlS.PL McLKlS.POS McLKlS.SRT McLKlS.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < McLKlS.cnt,
    hsortPtK 275 9 (mask 9) McLKlS.cnt McLKlS.T McLKlS.HS McLKlS.HSI i = true :=
  fun i hi => slK_spec sH i (Nat.zero_le _) (by omega) hi

theorem s_cl : ∀ c < McLKlS.cnt * (3 + 3), findPtK McLKlS.cnt McLKlS.T
    (prodQK 275 9 (mask 9) (3 + 3) McLKlS.T (bothK 3 McLKlS.GI McLKlSI)) McLKlCl c = true :=
  fun c hc => slK_spec sCl c (Nat.zero_le _) (by change c < Nat.mul McLKlS.cnt 6; omega)
    (by change c < Nat.mul McLKlS.cnt 6; omega)

theorem sift_eq {X : Nat} (hX : canonK 275 9 (mask 9) (275 * 9) X = true) :
    mclSift (tabT (unpack 275 9 X)) =
      siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) McLC.LR McLC.TRI McLC.BP 5 0 X := by
  unfold mclSift
  rw [natArr_tabT hX]
  exact CFSG.KC.J2Cover.siftK_eq McLK.binds McLK.hperm McLC.hl hX

theorem closure_eq : mulClosureH 275 sylAGens 200 = hRec 275 9 McLKlS.cnt McLKlS.T McLKlS.PL ∧
    mulTreeOK 275 sylAGens (hRec 275 9 McLKlS.cnt McLKlS.T McLKlS.PL).1
      (hRec 275 9 McLKlS.cnt McLKlS.T McLKlS.PL).2.1
      (hRec 275 9 McLKlS.cnt McLKlS.T McLKlS.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 McLKlS.cnt McLKlS.T McLKlS.PL).1.toList = true :=
  mulH_sound base.1 (fun j hj => (gen hj).2.2.1) s_tabs base.2.2.2.2.2 s_pe s_hs

theorem hT : ∀ i < McLKlS.cnt, canonK 275 9 (mask 9) (275 * 9) (McLKlS.T i) = true :=
  fun i hi => penumPt_canon (s_pe i hi)

theorem sub_ok : subEnumOK 275 200 8 mclSift sylAGens = true := by
  obtain ⟨e, ht, hd⟩ := closure_eq
  unfold subEnumOK
  simp only [Bool.and_eq_true]
  rw [e]
  refine ⟨⟨⟨⟨?_, ht⟩, closedOK_of hT (TabsOK_both s_tabs s_invs) s_cl⟩, hd⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 3 := by simpa [sylAGens] using hj
    have hx := tab hj'
    rw [getElem!_pos sylAGens j hj] at hx
    obtain ⟨c1, -, -, c4, c5⟩ := gen hj'
    rw [hx]
    simp only [Bool.and_eq_true]
    refine ⟨⟨permOK_unpack c1 c5, ?_⟩, ?_⟩
    · rw [sift_eq c1]
      exact allN_spec sift_ok j hj'
    · rw [invT_unpack (lt_of_canonK c4) c5]
      exact invOK_unpack c1 c4 c5
  · rw [hRec_size, base.2.2.2.2.1]
    exact beq_self_eq_true 8

theorem memKl_iff {cnt : Nat} {T : Nat → Nat} {x : Nat} :
    memKl cnt T x = true ↔ ∃ i < cnt, T i = x := by
  induction cnt with
  | zero => simp [memKl]
  | succ c ih =>
    change bIf(Nat.beq (T c) x, true, memKl c T x) = true ↔ _
    cases e : Nat.beq (T c) x
    · change memKl c T x = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h⟩
        · rw [h, Nat.beq_refl] at e
          exact Bool.noConfusion e
    · exact ⟨fun _ => ⟨c, by omega, Nat.eq_of_beq_eq_true e⟩, fun _ => rfl⟩

theorem memT_hRecKl {cnt : Nat} {T PL : Nat → Nat} {x : Nat}
    (hT : ∀ i < cnt, canonK 275 9 (mask 9) (275 * 9) (T i) = true)
    (hx : canonK 275 9 (mask 9) (275 * 9) x = true) :
    memT 275 (hRec 275 9 cnt T PL).1 (tabT (unpack 275 9 x)) = memKl cnt T x := by
  apply Bool.eq_iff_iff.2
  rw [memKl_iff]
  unfold memT
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    have hi' : i < cnt := by simpa [hRec] using hi
    have e : (hRec 275 9 cnt T PL).1[i] = tabT (unpack 275 9 (T i)) := by simp [hRec]
    rw [e, tblEq_unpack hx (hT i hi')] at h
    exact ⟨i, hi', (Nat.eq_of_beq_eq_true h).symm⟩
  · rintro ⟨i, hi, h⟩
    have hi' : i < (hRec 275 9 cnt T PL).1.size := by simpa [hRec] using hi
    refine ⟨i, hi', ?_⟩
    have e : (hRec 275 9 cnt T PL).1[i] = tabT (unpack 275 9 (T i)) := by simp [hRec]
    rw [e, h]
    exact tblEq_self hx

theorem hRec_entry {i : Nat} (hi : i < (hRec 275 9 McLKlS.cnt McLKlS.T McLKlS.PL).1.size) :
    (hRec 275 9 McLKlS.cnt McLKlS.T McLKlS.PL).1[i] = tabT (unpack 275 9 (McLKlS.T i)) ∧
      i < 8 := by
  have hi' : i < McLKlS.cnt := by simpa [hRec] using hi
  have h8 := base.2.2.2.2.1
  exact ⟨by simp [hRec], by omega⟩

theorem squares_ok :
    (mulClosureH 275 sylAGens 200).1.all (fun a => tblEq 275 (idT 275) (compT 275 a a)) = true := by
  rw [closure_eq.1, Array.all_eq_true]
  intro i hi
  obtain ⟨e, hi8⟩ := hRec_entry hi
  have h := allN_spec sSq i hi8
  simp only [bAnd_iff] at h
  have hc : canonK 275 9 (mask 9) (275 * 9) (McLKlS.T i) = true := h.1
  rw [e, compT_unpack hc hc, idT_tabT, ← idK_sound base.2.2.1,
    tblEq_unpack base.2.1 (canonK_pcomp hc hc)]
  exact h.2

theorem normalizes_ok :
    sylTwoGens.all (fun s => (mulClosureH 275 sylAGens 200).1.all (fun a =>
      memT 275 (mulClosureH 275 sylAGens 200).1 (compT 275 (compT 275 s a) (invT 275 s)))) =
      true := by
  rw [closure_eq.1, Array.all_eq_true]
  intro j hj
  have hj' : j < 7 := by simpa [sylTwoGens] using hj
  have hs := McLTwo.tab hj'
  rw [getElem!_pos sylTwoGens j hj] at hs
  obtain ⟨g1, -, -, g4, g5⟩ := McLTwo.gen hj'
  rw [hs, Array.all_eq_true]
  intro i hi
  obtain ⟨e, hi8⟩ := hRec_entry hi
  have hc : canonK 275 9 (mask 9) (275 * 9) (McLKlS.T i) = true :=
    hT i (by rw [base.2.2.2.2.1]; exact hi8)
  rw [e, invT_unpack (lt_of_canonK g1) g5, compT_unpack g1 hc,
    compT_unpack (canonK_pcomp g1 hc) g4, memT_hRecKl hT (canonK_pcomp (canonK_pcomp g1 hc) g4),
    base.2.2.2.2.1]
  exact allN_spec (allN_spec sNorm j hj') i hi8

end CertificateChecks.KernelSpor.McLKl

end
