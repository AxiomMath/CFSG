module

public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Data.Kernel.PerfWitK

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PerfWitK
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.GH74.Generic.S45

theorem size_tabT_unpack (n w q : Nat) : (tabT (unpack n w q)).size = n := by
  simp [tabT, unpack]

theorem map_compT {n : Nat} (P Q : Table) (hQ : Q.size = n) :
    Q.map (fun t => P[t.toNat]!) = compT n P Q := by
  unfold compT
  apply Array.ext (by simp [hQ])
  intro i h1 h2
  simp only [Array.getElem_map, Array.getElem_ofFn]
  rw [getElem!_pos Q i (by simpa using h1)]

theorem range_toArray_get {k i : Nat} (T : Nat → Table) (hi : i < k) :
    ((List.range k).map T).toArray[i]! = T i := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem lettersOK_append {k : Nat} {u v : List Int} (hu : lettersOK k u = true)
    (hv : lettersOK k v = true) : lettersOK k (u ++ v) = true := by
  unfold lettersOK at *
  rw [List.all_append, hu, hv]
  rfl

theorem lettersOK_invWord {k : Nat} {u : List Int} (hu : lettersOK k u = true) :
    lettersOK k (invWord u) = true := by
  simp only [lettersOK, invWord, List.all_eq_true, List.mem_reverse, List.mem_map] at hu ⊢
  rintro _ ⟨x, hx, rfl⟩
  simpa using hu x hx

theorem lettersOK_commW {k : Nat} {p : List Int × List Int} (h1 : lettersOK k p.1 = true)
    (h2 : lettersOK k p.2 = true) : lettersOK k (commW p) = true :=
  lettersOK_append (lettersOK_append (lettersOK_append h1 h2) (lettersOK_invWord h1))
    (lettersOK_invWord h2)

variable {n w k : Nat} {G GI : Nat → Nat} {T : Nat → Table}

theorem letter_unpack (hT : ∀ j < k, T j = tabT (unpack n w (G j)))
    (hG : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true ∧
      canonK n w (mask w) (n * w) (GI j) = true ∧ invEqK n w (mask w) (n * w) (G j) (GI j) = true)
    {l : Int} (h0 : l ≠ 0) (hl : l.natAbs ≤ k) :
    pwLetter n ((List.range k).map T).toArray l = tabT (unpack n w (letK G GI l)) ∧
      canonK n w (mask w) (n * w) (letK G GI l) = true := by
  unfold pwLetter
  cases l with
  | ofNat m =>
    have hm : m ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have hmk : m ≤ k := hl
    have hpos : (0 : Int) < Int.ofNat m := by
      rw [Int.ofNat_eq_coe]
      omega
    rw [if_pos hpos]
    have e : (Int.ofNat m).toNat = m := rfl
    rw [e, range_toArray_get T (by omega), hT (m - 1) (by omega)]
    exact ⟨rfl, (hG (m - 1) (by omega)).1⟩
  | negSucc m =>
    have hmk : m < k := by
      have : (Int.negSucc m).natAbs = m + 1 := rfl
      omega
    rw [if_neg (not_lt.2 (le_of_lt (Int.negSucc_lt_zero m)))]
    have e : (Int.negSucc m).natAbs - 1 = m := rfl
    obtain ⟨h1, h2, h3⟩ := hG m hmk
    rw [e, range_toArray_get T hmk, hT m hmk, invT_unpack (lt_of_canonK h1) h3]
    exact ⟨rfl, h2⟩

theorem word_unpack (hT : ∀ j < k, T j = tabT (unpack n w (G j)))
    (hG : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true ∧
      canonK n w (mask w) (n * w) (GI j) = true ∧ invEqK n w (mask w) (n * w) (G j) (GI j) = true)
    (hid : idT n = tabT (unpack n w (pidn n w)))
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true) :
    ∀ wd : List Int, lettersOK k wd = true →
      wordT n (pwLetter n ((List.range k).map T).toArray) wd = tabT (unpack n w (wK n w G GI wd)) ∧
        canonK n w (mask w) (n * w) (wK n w G GI wd) = true
  | [], _ => ⟨hid, hidc⟩
  | l :: rest, h => by
    have h' : (l != 0 && decide (l.natAbs ≤ k)) = true ∧ lettersOK k rest = true := by
      unfold lettersOK at h ⊢
      rwa [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hl, hr⟩ := h'
    rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hl
    obtain ⟨ih1, ih2⟩ := word_unpack hT hG hid hidc rest hr
    obtain ⟨L1, L2⟩ := letter_unpack hT hG hl.1 hl.2
    have e1 : wordT n (pwLetter n ((List.range k).map T).toArray) (l :: rest) =
        (wordT n (pwLetter n ((List.range k).map T).toArray) rest).map
          (fun t => (pwLetter n ((List.range k).map T).toArray l)[t.toNat]!) := rfl
    have e2 : wK n w G GI (l :: rest) = pcomp n w (mask w) (letK G GI l) (wK n w G GI rest) := rfl
    rw [e1, e2, ih1, L1, map_compT _ _ (size_tabT_unpack n w _), compT_unpack L2 ih2]
    exact ⟨rfl, canonK_pcomp L2 ih2⟩

theorem perfWitOK_of {W : PerfWit}
    (hidA : CFSG.Monster.B.Co2.Native.idA n = unpack n w (pidn n w))
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hT : ∀ j < k, T j = tabT (unpack n w (G j)))
    (hG : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true ∧
      canonK n w (mask w) (n * w) (GI j) = true ∧ invEqK n w (mask w) (n * w) (G j) (GI j) = true)
    (h : perfK n w k G GI W = true) : perfWitOK n ((List.range k).map T) W = true := by
  have hid : idT n = tabT (unpack n w (pidn n w)) := by rw [idT_tabT, hidA]
  unfold perfK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hcomm⟩, hl4⟩, hord⟩ := h
  unfold perfWitOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.length_map, List.length_range, beq_iff_eq]
  refine ⟨⟨⟨⟨Nat.eq_of_beq_eq_true hlen, ?_⟩, ?_⟩, hl4⟩, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    have hj' := List.mem_range.1 hj
    obtain ⟨h1, h2, h3⟩ := hG j hj'
    rw [hT j hj', invT_unpack (lt_of_canonK h1) h3]
    exact ⟨permOK_unpack h1 h3, invOK_unpack h1 h2 h3⟩
  · intro i hi
    have hi' := List.mem_range.1 hi
    obtain ⟨⟨a1, a2⟩, a3⟩ := hcomm i hi
    refine ⟨⟨a1, a2⟩, ?_⟩
    obtain ⟨w1, w2⟩ := word_unpack hT hG hid hidc (commW W.comms[i]!) (lettersOK_commW a1 a2)
    change tblEq n _ (wordT n _ (commW W.comms[i]!)) = true
    rw [range_toArray_get T hi', hT i hi', w1, tblEq_unpack (hG i hi').1 w2]
    exact a3
  · obtain ⟨w1, w2⟩ := word_unpack hT hG hid hidc W.four hl4
    rw [w1, ordTest_unpack (P := powK n w (wK n w G GI W.four)) ⟨rfl, fun _ => rfl⟩ hidA hidc w2]
    exact hord

end CFSG.KS.MulH

end
