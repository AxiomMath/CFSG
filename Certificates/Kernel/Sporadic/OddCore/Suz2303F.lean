module

public import Certificates.Kernel.Sporadic.OddCore.Suz2303
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.KC.Enum
open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Mathieu CFSG.KC.Misc.HexAt
open CFSG.KC.BfsPin CertificateChecks.KernelSpor.Suz2306

theorem szOK1782 : szOK 1782 11 = true := by
  quickRfl

theorem gens_all {ρ : Nat} (hρ : ρ < 11) : recGensK ρ = true := by
  interval_cases ρ
  exacts [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]

theorem enum_all {ρ : Nat} (hρ : ρ < 11) : recEnumK ρ = true := by
  interval_cases ρ
  exacts [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10]

theorem blk_get {f : Nat → Bool} {lo len k : Nat} (h : allBlk lo f len = true) (h1 : lo ≤ k)
    (h2 : k < lo + len) : f k = true := by
  have := allBlk_spec h (k - lo) (by omega)
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rwa [e] at this

theorem elem_all {ρ k : Nat} (hρ : ρ < 11) (hk : k < nget recO ρ) : elemPt ρ k = true := by
  interval_cases ρ
  · exact blk_get e0 (Nat.zero_le _) hk
  · exact blk_get e1 (Nat.zero_le _) hk
  · exact blk_get e2 (Nat.zero_le _) hk
  · change k < 81 at hk
    rcases Nat.lt_or_ge k 14 with h | h
    · exact blk_get e3a (Nat.zero_le _) h
    rcases Nat.lt_or_ge k 28 with h' | h'
    · exact blk_get e3b h h'
    rcases Nat.lt_or_ge k 42 with h'' | h''
    · exact blk_get e3c h' h''
    rcases Nat.lt_or_ge k 56 with h3 | h3
    · exact blk_get e3d h'' h3
    rcases Nat.lt_or_ge k 70 with h4 | h4
    · exact blk_get e3e h3 h4
    · exact blk_get e3f h4 (by omega)
  · exact blk_get e4 (Nat.zero_le _) hk
  · change k < 27 at hk
    rcases Nat.lt_or_ge k 14 with h | h
    · exact blk_get e5a (Nat.zero_le _) h
    · exact blk_get e5b h (by omega)
  · exact blk_get e6 (Nat.zero_le _) hk
  · exact blk_get e7 (Nat.zero_le _) hk
  · change k < 27 at hk
    rcases Nat.lt_or_ge k 14 with h | h
    · exact blk_get e8a (Nat.zero_le _) h
    · exact blk_get e8b h (by omega)
  · change k < 25 at hk
    rcases Nat.lt_or_ge k 13 with h | h
    · exact blk_get e9a (Nat.zero_le _) h
    · exact blk_get e9b h (by omega)
  · exact blk_get e10 (Nat.zero_le _) hk

theorem line_all {ρ l : Nat} (hρ : ρ < 11) (hl : l < nget recL ρ) : linePt ρ l = true := by
  interval_cases ρ
  · exact blk_get l0 (Nat.zero_le _) hl
  · exact blk_get l1 (Nat.zero_le _) hl
  · exact blk_get l2 (Nat.zero_le _) hl
  · change l < 22 at hl
    rcases Nat.lt_or_ge l 6 with h | h
    · exact blk_get l3a (Nat.zero_le _) h
    rcases Nat.lt_or_ge l 12 with h' | h'
    · exact blk_get l3b h h'
    rcases Nat.lt_or_ge l 18 with h'' | h''
    · exact blk_get l3c h' h''
    · exact blk_get l3d h'' (by omega)
  · exact blk_get l4 (Nat.zero_le _) hl
  · change l < 13 at hl
    rcases Nat.lt_or_ge l 5 with h | h
    · exact blk_get l5a (Nat.zero_le _) h
    rcases Nat.lt_or_ge l 10 with h' | h'
    · exact blk_get l5b h h'
    · exact blk_get l5c h' (by omega)
  · exact blk_get l6 (Nat.zero_le _) hl
  · exact blk_get l7 (Nat.zero_le _) hl
  · change l < 13 at hl
    rcases Nat.lt_or_ge l 5 with h | h
    · exact blk_get l8a (Nat.zero_le _) h
    rcases Nat.lt_or_ge l 10 with h' | h'
    · exact blk_get l8b h h'
    · exact blk_get l8c h' (by omega)
  · exact blk_get l9 (Nat.zero_le _) hl
  · exact blk_get l10 (Nat.zero_le _) hl

theorem lgetA_eq {α : Type} (d : α) (L : List α) (i : Nat) : lgetA d L i = L.getD i d := by
  induction L generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem nget_eq' (l : List Nat) (i : Nat) : nget l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem rec_shape {ρ : Nat} (hρ : ρ < 11) :
    oddShape (nget recEnt ρ) (nget recR ρ) =
      [nget recP ρ, nget recO ρ, nget recG ρ, nget recL ρ] ∧
    invOddRecordStart (nget recEnt ρ) (nget recR ρ) = nget recS ρ ∧
    nget recS ρ + nget recG ρ + nget recL ρ ≤ invRunCount (nget recEnt ρ) ∧
    nget recEnt ρ < 4 ∧
    invInnerStart (nget recEnt ρ) = nget innS (nget recEnt ρ) := by
  interval_cases ρ <;> decide

theorem rec_words {ρ : Nat} (hρ : ρ < 11) : ∀ l < nget recL ρ,
    oddWord (nget recEnt ρ) (nget recR ρ) l = oddWordK ρ l ∧
    oddOrder (nget recEnt ρ) (nget recR ρ) l = oddOrdK ρ l ∧
    (∀ h ∈ oddWordK ρ l, 1 ≤ h ∧ h ≤ (invInnerGenArrs (nget recEnt ρ)).size) := by
  interval_cases ρ <;> decide

theorem canon_of_perm {p q : Nat} (h : invEqK 1782 11 (mask 11) (1782 * 11) p q = true) :
    canonK 1782 11 (mask 11) (1782 * 11) p = true := by
  have h' : bAnd(Nat.beq (Nat.shiftRight p (1782 * 11)) (nat_lit 0),
      bAnd(Nat.beq (Nat.shiftRight q (1782 * 11)) (nat_lit 0),
      allN 1782 (fun i => strictB (pg 11 (mask 11) p i) (fun v =>
        bAnd(Nat.blt v 1782, Nat.beq (pg 11 (mask 11) q v) i))))) = true := h
  obtain ⟨h1, -, h3⟩ := (by simpa only [bAnd_iff] using h' :
    Nat.beq (Nat.shiftRight p (1782 * 11)) (nat_lit 0) = true ∧
    Nat.beq (Nat.shiftRight q (1782 * 11)) (nat_lit 0) = true ∧
    allN 1782 (fun i => strictB (pg 11 (mask 11) p i) (fun v =>
      bAnd(Nat.blt v 1782, Nat.beq (pg 11 (mask 11) q v) i))) = true)
  change bAnd(szOK 1782 11, bAnd(Nat.beq (Nat.shiftRight p (1782 * 11)) (nat_lit 0),
    allN 1782 (fun i => Nat.blt (pg 11 (mask 11) p i) 1782))) = true
  rw [szOK1782, h1]
  apply allN_of
  intro i hi
  have := allN_spec h3 i hi
  rw [strictB_app] at this
  exact ((bAnd_iff _ _).1 this).1

theorem canon_ppow {t : Nat} (ht : canonK 1782 11 (mask 11) (1782 * 11) t = true) :
    ∀ e, canonK 1782 11 (mask 11) (1782 * 11) (ppow 1782 11 (mask 11) (pidn 1782 11) t e) = true
  | 0 => hid.1
  | e + 1 => by
    change canonK 1782 11 (mask 11) (1782 * 11) (strictN (ppow 1782 11 (mask 11) (pidn 1782 11) t e)
      (fun q => pcomp 1782 11 (mask 11) t q)) = true
    rw [strictN_app']
    exact canonK_pcomp ht (canon_ppow ht e)

theorem powA_unpack {t : Nat} (ht : canonK 1782 11 (mask 11) (1782 * 11) t = true) (e : Nat) :
    powA 1782 (unpack 1782 11 t) e = unpack 1782 11 (ppow 1782 11 (mask 11) (pidn 1782 11) t e) := by
  rw [powA_eq]
  refine powEqK_sound ?_
  change bAnd(canonK 1782 11 (mask 11) (1782 * 11) t,
    Nat.beq (ppow 1782 11 (mask 11) (pidn 1782 11) t e) (ppow 1782 11 (mask 11) (pidn 1782 11) t e)) = true
  rw [ht, Nat.beq_refl]

theorem idA_eq : idA 1782 = unpack 1782 11 (pidn 1782 11) := (idK_sound hid.2).symm

theorem gen_get {ρ k : Nat} (hρ : ρ < 11) (hk : k < nget recG ρ) :
    (invOddGenArrs (nget recEnt ρ) (nget recR ρ))[k]! = unpack 1782 11 (genP ρ k) := by
  obtain ⟨hs, hst, hc, he, -⟩ := rec_shape hρ
  have hsize : ((invOddCoreShapes.getD (nget recEnt ρ) []).getD (nget recR ρ) []).getD 2 0 =
      nget recG ρ := by
    have := congrArg (fun l : List Nat => l.getD 2 0) hs
    simpa [oddShape] using this
  rw [getElem!_pos _ k (by rw [invOddGenArrs, Array.size_ofFn, hsize]; exact hk)]
  simp only [invOddGenArrs, Array.getElem_ofFn]
  rw [hst, run_all he (by omega)]
  rfl

theorem line_get {ρ l : Nat} (hρ : ρ < 11) (hl : l < nget recL ρ) :
    (invOddLineArrs (nget recEnt ρ) (nget recR ρ))[l]! = unpack 1782 11 (lineP ρ l) := by
  obtain ⟨hs, hst, hc, he, -⟩ := rec_shape hρ
  have hsize : ((invOddCoreShapes.getD (nget recEnt ρ) []).getD (nget recR ρ) []).getD 3 0 =
      nget recL ρ := by
    have := congrArg (fun l : List Nat => l.getD 3 0) hs
    simpa [oddShape] using this
  have hsize2 : ((invOddCoreShapes.getD (nget recEnt ρ) []).getD (nget recR ρ) []).getD 2 0 =
      nget recG ρ := by
    have := congrArg (fun l : List Nat => l.getD 2 0) hs
    simpa [oddShape] using this
  rw [getElem!_pos _ l (by rw [invOddLineArrs, Array.size_ofFn, hsize]; exact hl)]
  simp only [invOddLineArrs, Array.getElem_ofFn]
  rw [hst, hsize2, run_all he (by omega)]
  rfl

theorem inner_get {i h : Nat} (hi : i < 4) (h1 : 1 ≤ h) (h2 : h ≤ (invInnerGenArrs i).size) :
    (invInnerGenArrs i)[h - 1]! = unpack 1782 11 (innP i h) ∧
      canonK 1782 11 (mask 11) (1782 * 11) (innP i h) = true := by
  have hsz : (invInnerGenArrs i).size = invInnerGenCounts.getD i 0 := by
    simp [invInnerGenArrs]
  have hb : invInnerStart i + invInnerGenCounts.getD i 0 ≤ invRunCount i ∧
      invInnerStart i = nget innS i := by
    interval_cases i <;> decide
  have hk : invInnerStart i + (h - 1) < invRunCount i := by omega
  have e : invRun i (invInnerStart i + (h - 1)) = unpack 1782 11 (innP i h) := by
    rw [run_all hi hk]
    unfold innP
    congr 2
    change invInnerStart i + (h - 1) = nget innS i + h - 1
    omega
  refine ⟨?_, ?_⟩
  · rw [getElem!_pos _ (h - 1) (by omega)]
    simp only [invInnerGenArrs, Array.getElem_ofFn]
    exact e
  · obtain ⟨r, hr⟩ := perm_all hi hk
    have e2 : innP i h = runP i (invInnerStart i + (h - 1)) := by
      unfold innP
      congr 1
      change nget innS i + h - 1 = invInnerStart i + (h - 1)
      omega
    rw [e2]
    exact canon_of_perm hr

theorem innerWord_eq {i : Nat} (hi : i < 4) :
    ∀ w : List Nat, (∀ h ∈ w, 1 ≤ h ∧ h ≤ (invInnerGenArrs i).size) →
      innerWordArr i w = unpack 1782 11 (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP i) w) ∧
        canonK 1782 11 (mask 11) (1782 * 11)
          (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP i) w) = true
  | [], _ => by
    have e : wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP i) [] = pidn 1782 11 := rfl
    have e2 : innerWordArr i [] = idA 1782 := by
      unfold innerWordArr
      rw [List.foldr_nil]
    rw [e, e2]
    exact ⟨idA_eq, hid.1⟩
  | h :: rest, hw => by
    obtain ⟨ih1, ih2⟩ := innerWord_eq hi rest (fun h' hh => hw h' (List.mem_cons_of_mem h hh))
    obtain ⟨h1, h2⟩ := hw h List.mem_cons_self
    obtain ⟨g1, g2⟩ := inner_get hi h1 h2
    have e : wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP i) (h :: rest) =
        pcomp 1782 11 (mask 11) (innP i h) (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP i) rest) := by
      change strictN (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP i) rest)
        (fun acc => pcomp 1782 11 (mask 11) (innP i h) acc) = _
      rw [strictN_app']
    have e2 : innerWordArr i (h :: rest) =
        compA 1782 (invInnerGenArrs i)[h - 1]! (innerWordArr i rest) := by
      unfold innerWordArr
      rw [List.foldr_cons]
    rw [e, e2, ih1, g1]
    exact ⟨compA_unpack g2 ih2, canonK_pcomp g2 ih2⟩

theorem rec_get1782 {cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (penumRec 1782 11 cnt T PL).tabs[i]! = unpack 1782 11 (T i) := by
  rw [getElem!_pos _ i (by simp only [penumRec, Array.size_ofFn]; exact hi)]
  simp only [penumRec, Array.getElem_ofFn]

theorem eqA_u {p q : Nat} (hp : canonK 1782 11 (mask 11) (1782 * 11) p = true)
    (hq : canonK 1782 11 (mask 11) (1782 * 11) q = true) :
    eqA 1782 (unpack 1782 11 p) (unpack 1782 11 q) = Nat.beq p q :=
  eqA_unpack hp hq

theorem gens_facts {ρ k : Nat} (hρ : ρ < 11) (hk : k < nget recG ρ) :
    OEF.G (Nat.add (OEF.GO ρ) k) = genP ρ k ∧
      invEqK 1782 11 (mask 11) (1782 * 11) (genP ρ k) (pinvS 1782 11 (mask 11) (genP ρ k)) = true ∧
      msift (genP ρ k) = true ∧
      commK 1782 11 (mask 11) (1782 * 11) (genP ρ k) (SuzTP (nget recEnt ρ)) = true := by
  have h := gens_all hρ
  unfold recGensK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, h3⟩ := h
  have h4 := allN_spec h3 k hk
  rw [strictB_app] at h4
  obtain ⟨a, b, c, d⟩ := (by simpa only [bAnd_iff] using h4 :
    Nat.beq (OEF.G (Nat.add (OEF.GO ρ) k)) (genP ρ k) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) (genP ρ k) (pinvS 1782 11 (mask 11) (genP ρ k)) = true ∧
    msift (genP ρ k) = true ∧
    commK 1782 11 (mask 11) (1782 * 11) (genP ρ k) (SuzTP (nget recEnt ρ)) = true)
  exact ⟨Nat.eq_of_beq_eq_true a, b, c, d⟩

theorem gens_counts {ρ : Nat} (hρ : ρ < 11) :
    OEF.K ρ = nget recG ρ ∧ OEF.C ρ = nget recO ρ := by
  have h := gens_all hρ
  unfold recGensK at h
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1⟩

theorem line_facts {ρ l : Nat} (hρ : ρ < 11) (hl : l < nget recL ρ) :
    invEqK 1782 11 (mask 11) (1782 * 11) (lineP ρ l) (pinvS 1782 11 (mask 11) (lineP ρ l)) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11)
      (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP (nget recEnt ρ)) (oddWordK ρ l))
      (pinvS 1782 11 (mask 11)
        (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP (nget recEnt ρ)) (oddWordK ρ l))) = true ∧
    canonK 1782 11 (mask 11) (1782 * 11) (pinvS 1782 11 (mask 11)
        (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP (nget recEnt ρ)) (oddWordK ρ l))) = true ∧
    (∀ W, W = ppow 1782 11 (mask 11) (pidn 1782 11)
        (pcomp 1782 11 (mask 11) (lineP ρ l) (pcomp 1782 11 (mask 11)
          (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP (nget recEnt ρ)) (oddWordK ρ l))
          (pcomp 1782 11 (mask 11) (lineP ρ l) (pinvS 1782 11 (mask 11)
            (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP (nget recEnt ρ)) (oddWordK ρ l))))))
        (Nat.div (oddOrdK ρ l) 2) →
      canonK 1782 11 (mask 11) (1782 * 11) W = true ∧
      Nat.beq (pcomp 1782 11 (mask 11) W W) (pidn 1782 11) = true ∧
      bIf(Nat.beq W (pidn 1782 11), false, true) = true) := by
  have h := line_all hρ hl
  unfold linePt at h
  simp only [strictB_app] at h
  obtain ⟨a, b, c, d, e, f⟩ := (by simpa only [bAnd_iff] using h)
  exact ⟨a, b, c, fun W hW => by subst hW; exact ⟨d, e, f⟩⟩

theorem bIf_ne {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem rec_ok {ρ : Nat} (hρ : ρ < 11) :
    oddRecordOK (nget recEnt ρ) (nget recR ρ) (oddEnum (nget recEnt ρ) (nget recR ρ)) = true := by
  obtain ⟨hs, -, -, he, -⟩ := rec_shape hρ
  obtain ⟨hK, hC⟩ := gens_counts hρ
  have hgsz : (invOddGenArrs (nget recEnt ρ) (nget recR ρ)).size = nget recG ρ := by
    have := congrArg (fun l : List Nat => l.getD 2 0) hs
    simp only [invOddGenArrs, Array.size_ofFn]
    simpa [oddShape] using this
  have hlsz : (invOddLineArrs (nget recEnt ρ) (nget recR ρ)).size = nget recL ρ := by
    have := congrArg (fun l : List Nat => l.getD 3 0) hs
    simp only [invOddLineArrs, Array.size_ofFn]
    simpa [oddShape] using this
  have hp : (oddShape (nget recEnt ρ) (nget recR ρ)).getD 0 0 = nget recP ρ := by
    rw [hs]
    rfl
  have hcap : (oddShape (nget recEnt ρ) (nget recR ρ)).getD 1 0 = nget recO ρ := by
    rw [hs]
    rfl
  have hgok : GensOK 1782 11 (OEF.K ρ) (offF OEF.G (OEF.GO ρ))
      (invOddGenArrs (nget recEnt ρ) (nget recR ρ)) := by
    refine ⟨by rw [hgsz, hK], fun k hk => ?_⟩
    rw [hK] at hk
    obtain ⟨a, b, -, -⟩ := gens_facts hρ hk
    refine ⟨?_, ?_⟩
    · rw [gen_get hρ hk]
      change unpack 1782 11 (genP ρ k) = unpack 1782 11 (OEF.G (Nat.add (OEF.GO ρ) k))
      rw [a]
    · change canonK 1782 11 (mask 11) (1782 * 11) (OEF.G (Nat.add (OEF.GO ρ) k)) = true
      rw [a]
      exact canon_of_perm b
  have hen := enum_all hρ
  unfold recEnumK at hen
  obtain ⟨hhd, hsl⟩ := (bAnd_iff _ _).1 hen
  have hpt : ∀ k < OEF.C ρ, penumPtK 1782 11 (mask 11) (1782 * 11) false (offF OEF.G (OEF.GO ρ))
      (offF OEF.G (OEF.GO ρ)) (OEF.K ρ) (OEF.C ρ) (offF OEF.T (OEF.TO ρ)) (offF OEF.PL (OEF.PLO ρ))
      (offF OEF.POS (OEF.POSO ρ)) (offF OEF.SRT (OEF.SRTO ρ)) (offF OEF.SRI (OEF.SRIO ρ)) k = true :=
    fun k hk => penumSl_spec hsl k (Nat.zero_le _) (by omega) hk
  have hE := penumK_left_sound (cap := nget recO ρ) szOK1782 hgok hhd hpt
  have hoE : oddEnum (nget recEnt ρ) (nget recR ρ) =
      penumRec 1782 11 (OEF.C ρ) (offF OEF.T (OEF.TO ρ)) (offF OEF.PL (OEF.PLO ρ)) := by
    unfold oddEnum enumBFS
    rw [hcap]
    exact hE.1
  rw [hoE]
  unfold oddRecordOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, hE.2⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold allBelow
    rw [all_range_iff, hgsz]
    intro k hk
    obtain ⟨-, b, c, d⟩ := gens_facts hρ hk
    rw [gen_get hρ hk]
    simp only [Bool.and_eq_true]
    refine ⟨⟨permOK_unpack b, ?_⟩, ?_⟩
    · rw [inM_eq rfl (canon_of_perm b)]
      exact c
    · rw [(rep_facts he).1]
      exact commutes_eq d
  · rw [hcap]
    simp only [penumRec, Array.size_ofFn]
    exact hC
  · unfold allBelow
    rw [all_range_iff]
    intro k hk
    have hk' : k < OEF.C ρ := by simpa [penumRec] using hk
    have ht := penumPt_canon (hpt k hk')
    rw [rec_get1782 hk', hp, powA_unpack ht, idA_eq, eqA_u (canon_ppow ht _) hid.1, eqA_u ht hid.1]
    have hel := elem_all hρ (by rw [← hC]; exact hk')
    unfold elemPt at hel
    rw [strictB_app] at hel
    cases h1 : Nat.beq (ppow 1782 11 (mask 11) (pidn 1782 11) (offF OEF.T (OEF.TO ρ) k) (nget recP ρ))
        (pidn 1782 11)
    · simp
    · rw [h1] at hel
      cases h2 : Nat.beq (offF OEF.T (OEF.TO ρ) k) (pidn 1782 11)
      · rw [h2] at hel
        simp only [strictB_app] at hel
        obtain ⟨hj, hl, hw⟩ := (by simpa only [bAnd_iff] using hel :
          Nat.blt (Nat.shiftRight (OW (Nat.add (OWO ρ) k)) 8) (nget recP ρ) = true ∧
          Nat.blt (Nat.land (OW (Nat.add (OWO ρ) k)) 255) (nget recL ρ) = true ∧
          Nat.beq (ppow 1782 11 (mask 11) (pidn 1782 11) (offF OEF.T (OEF.TO ρ) k)
            (Nat.shiftRight (OW (Nat.add (OWO ρ) k)) 8))
            (lineP ρ (Nat.land (OW (Nat.add (OWO ρ) k)) 255)) = true)
        have hj' := Eq.mp Nat.blt_eq hj
        have hl' := Eq.mp Nat.blt_eq hl
        simp only [Bool.not_true, Bool.false_or]
        unfold anyBelow
        rw [List.any_eq_true]
        refine ⟨Nat.shiftRight (OW (Nat.add (OWO ρ) k)) 8, List.mem_range.2 hj', ?_⟩
        rw [List.any_eq_true]
        refine ⟨Nat.land (OW (Nat.add (OWO ρ) k)) 255, List.mem_range.2 (by rw [hlsz]; exact hl'), ?_⟩
        rw [line_get hρ hl', powA_unpack ht,
          eqA_u (canon_ppow ht _) (canon_of_perm (line_facts hρ hl').1)]
        exact hw
      · simp
  · unfold allBelow
    rw [all_range_iff, hlsz]
    intro l hl
    obtain ⟨w1, w2, w3⟩ := rec_words hρ l hl
    obtain ⟨fx, fg, fgi, fw⟩ := line_facts hρ hl
    have hx := canon_of_perm fx
    obtain ⟨g1, g2⟩ := innerWord_eq he _ w3
    obtain ⟨wc, ww, wn⟩ := fw _ rfl
    unfold oddLineOK
    simp only [Bool.and_eq_true]
    rw [line_get hρ hl, w1, g1, invCand_unpack fg, w2]
    unfold xgxgArr
    have hdiv : oddOrdK ρ l / 2 = Nat.div (oddOrdK ρ l) 2 := rfl
    rw [hdiv, compA_unpack hx fgi, compA_unpack g2 (canonK_pcomp hx fgi),
      compA_unpack hx (canonK_pcomp g2 (canonK_pcomp hx fgi)),
      powA_unpack (canonK_pcomp hx (canonK_pcomp g2 (canonK_pcomp hx fgi))), compA_unpack wc wc, idA_eq,
      eqA_u (canonK_pcomp wc wc) hid.1, eqA_u wc hid.1, bIf_ne wn]
    refine ⟨⟨⟨⟨permOK_unpack fx, ?_⟩, (invEqK_sound fg).2⟩, ww⟩, rfl⟩
    rw [List.all_eq_true]
    intro h hh
    simpa using w3 h hh

theorem facts2303 : oddEntryOK 0 = true ∧ oddEntryOK 1 = true ∧ oddEntryOK 2 = true ∧
    oddEntryOK 3 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold oddEntryOK allBelow <;> rw [all_range_iff] <;> intro r hr
  · have hr' : r < 3 := hr
    interval_cases r
    exacts [rec_ok (ρ := 0) (by omega), rec_ok (ρ := 1) (by omega), rec_ok (ρ := 2) (by omega)]
  · have hr' : r < 2 := hr
    interval_cases r
    exacts [rec_ok (ρ := 3) (by omega), rec_ok (ρ := 4) (by omega)]
  · have hr' : r < 3 := hr
    interval_cases r
    exacts [rec_ok (ρ := 5) (by omega), rec_ok (ρ := 6) (by omega), rec_ok (ρ := 7) (by omega)]
  · have hr' : r < 3 := hr
    interval_cases r
    exacts [rec_ok (ρ := 8) (by omega), rec_ok (ρ := 9) (by omega), rec_ok (ρ := 10) (by omega)]

end CertificateChecks.KernelSpor.OddCore

end
