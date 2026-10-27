module

public import Certificates.Kernel.SporSch.Ru.T2259K
public import CFSG.Certificates.Kernel.SporSch.RuTreeSound
public import CFSG.Certificates.Kernel.SporSch.RuTreeSetsSound

public section

namespace CertificateChecks.KernelSporSch.Ru2259

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.RuTree CFSG.KLC.Fi22 CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuTree CFSG.Sporadic.RuSchreier CFSG.Certificates.Native
  CFSG.Monster.B.Co2.Native

@[expose] def Good (j x : Nat) : Prop :=
  (∀ p, (x >>> 4096).testBit p = true ↔ p ∈ ruTreeSets[j]!) ∧ ∀ p ∈ ruTreeSets[j]!, p < 4060

theorem unpack_get! {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem arr_spec {NW A : Nat} (hv : nwValid NW = true) (h : arrK NW A = true) :
    (∀ s < 4096, CFSG.KC.Benes.nwInv NW s = if s < 4060 then (unpack 4060 12 A)[s]! else s) ∧
      ∀ s < 4060, (unpack 4060 12 A)[s]! < 4060 := by
  have key : ∀ s < 4096, CFSG.KC.Benes.nwInv NW s =
      (if s < 4060 then pg 12 (mask 12) A s else s) ∧ (s < 4060 → CFSG.KC.Benes.nwInv NW s < 4060) := by
    intro s hs
    have h1 := rngK_spec h s (Nat.zero_le s) (by omega)
    dsimp only at h1
    obtain ⟨h2, h3⟩ := andB_iff'.1 h1
    have e : Nat.land (Nat.shiftRight (arrInvNW NW) (Nat.mul 16 s)) 65535 =
        CFSG.KC.Benes.nwInv NW s := by
      rw [← CFSG.KC.Benes.arrInvNW_entry hv hs]
      change (arrInvNW NW >>> (16 * s)) &&& 65535 = _
      rw [Nat.shiftRight_eq_div_pow, show (65535 : Nat) = 2 ^ 16 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    rw [e] at h2 h3
    have h4 := Nat.eq_of_beq_eq_true h2
    rw [bnat] at h4
    refine ⟨?_, fun hl => ?_⟩
    · by_cases hl : s < 4060
      · simp only [Nat.blt_eq.mpr hl, ↓reduceIte] at h4
        simp only [hl, ↓reduceIte]
        exact h4
      · have hb : ¬ (Nat.blt s 4060 = true) := by rw [Nat.blt_eq]; exact hl
        simp only [hb] at h4
        simp only [hl, ↓reduceIte]
        exact h4
    · rcases orB_iff'.1 h3 with h5 | h5
      · have : Nat.blt s 4060 = true := Nat.blt_eq.mpr hl
        rw [this] at h5
        exact absurd h5 (by decide)
      · exact Nat.blt_eq.mp h5
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [(key s hs).1]
    by_cases hl : s < 4060
    · simp only [hl, ↓reduceIte, unpack_get! hl]
    · simp only [hl, ↓reduceIte]
  · have := (key s (by omega)).2 hs
    rw [(key s (by omega)).1] at this
    simp only [hs, ↓reduceIte] at this
    rw [unpack_get! hs]
    exact this

theorem shr4 (x : Nat) : x >>> 4 = x / 16 := Nat.shiftRight_eq_div_pow x 4

theorem allLt_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    CFSG.Monster.B.Co2.Native.allLt n p = true := by
  unfold CFSG.Monster.B.Co2.Native.allLt
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.all_succ, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (by omega), h n (by omega)⟩

theorem lenK_eq : ∀ l : List Nat, lenK l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenK l) = _
    rw [lenK_eq l]
    rfl

theorem mskK_testBit : ∀ (l : List Nat) (p : Nat), (mskK l).testBit p = true ↔ p ∈ l
  | [], p => by simp [mskK]
  | a :: l, p => by
    change (Nat.lor (Nat.shiftLeft 1 a) (mskK l)).testBit p = true ↔ _
    rw [show Nat.lor (Nat.shiftLeft 1 a) (mskK l) = (1 <<< a) ||| mskK l from rfl,
      Nat.testBit_or, Bool.or_eq_true, mskK_testBit l p, List.mem_cons, Nat.one_shiftLeft,
      Nat.testBit_two_pow]
    simp only [decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem fixL_eq (Z : Nat) : ∀ n, fixL Z n = (List.range n).filter (fun p => pg 12 (mask 12) Z p == p)
  | 0 => rfl
  | n + 1 => by
    change Bool.rec (motive := fun _ => List Nat) (fixL Z n) (List.append (fixL Z n) [n])
      (Nat.beq (pg 12 (mask 12) Z n) n) = _
    rw [List.range_succ, List.filter_append, fixL_eq Z n]
    cases h : Nat.beq (pg 12 (mask 12) Z n) n
    · have : (pg 12 (mask 12) Z n == n) = false := h
      simp [List.filter, this]
    · have : (pg 12 (mask 12) Z n == n) = true := h
      simp [List.filter, this]

theorem fixZ_eq : ruFixZ = fixL RuG.Z 4060 := by
  rw [fixL_eq, ruFixZ, fixedList, RuG.z_eq]
  apply List.filter_congr
  intro p hp
  rw [unpack_get! (List.mem_range.1 hp)]

theorem facts (hb : ∀ i < 232, blk i = true) (hp : ∀ i < 145, pblk i = true) :
    ruFixZ.length = 92 ∧ ruTreeSets.size = 593775 ∧
    (∀ j, 1 ≤ j → j < 593775 → ruTreeParent j < j ∧ ruTreeGen j < 2) ∧
    translatesOK ruTreeGens ruFixZ ruTreeSets ruTreePar ruTreeLab = true ∧
    ruSortedStrict ruTreeSets = true := by
  obtain ⟨hsz, hs0, hsj⟩ := ruTreeSets_spec
  have hfix : ruFixZ = fixL RuG.Z 4060 := fixZ_eq
  obtain ⟨g0, g0'⟩ := arr_spec nw0 arr0
  obtain ⟨g1, g1'⟩ := arr_spec nw1 arr1
  have hgen : ∀ l < 2, ruTreeGens[l]! = if l = 1 then unpack 4060 12 RuG.A1 else unpack 4060 12 RuG.A0 := by
    intro l hl
    rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
    · have e : ruTreeGens[0]! = ruA0A := by simp [ruTreeGens]
      simp only [e, show (0 : Nat) ≠ 1 by decide, ↓reduceIte]
      exact RuG.a0_eq
    · have e : ruTreeGens[1]! = ruA1A := by simp [ruTreeGens]
      simp only [e, ↓reduceIte]
      exact RuG.a1_eq
  have hpar : ∀ j, 1 ≤ j → j < 593775 → ruTreePar[j]! = plK j >>> 4 := by
    intro j h1 h2
    rw [ruTreePar, getElem!_pos _ j (by simpa using h2), Array.getElem_ofFn]
    simp only [show j ≠ 0 by omega, ↓reduceIte]
    rw [(pl_spec h1 h2).1, shr4]
  have hlab : ∀ j, 1 ≤ j → j < 593775 → ruTreeLab[j]! = plK j % 16 := by
    intro j h1 h2
    rw [ruTreeLab, getElem!_pos _ j (by simpa using h2), Array.getElem_ofFn]
    simp only [show j ≠ 0 by omega, ↓reduceIte]
    rw [(pl_spec h1 h2).2]
  have hG0 : Good 0 RuTD.F0 := by
    have e0 : RuTD.F0 >>> 4096 = mskK (fixL RuG.Z 4060) := Nat.eq_of_beq_eq_true f0
    unfold Good
    rw [hs0, hfix, e0]
    refine ⟨fun p => mskK_testBit _ p, fun p hp => ?_⟩
    rw [fixL_eq] at hp
    exact List.mem_range.1 (List.mem_filter.1 hp).1
  have hstep : ∀ c, 1 ≤ c → c < 593775 → plK c >>> 4 < c → plK c % 16 < 2 → ∀ x,
      Good (plK c >>> 4) x → Good c (mv RuTD.NW0 RuTD.NW1 (plK c) x) := by
    intro c h1 h2 h3 h4 x ⟨hx1, hx2⟩
    have e := hsj c h1 h2 (by rw [hpar c h1 h2]; exact h3)
    rw [hpar c h1 h2, hlab c h1 h2] at e
    rw [Good, e, mv_hi nw0 nw1]
    have hbit2 : plK c % 2 = plK c % 16 := by omega
    have himg : ∀ (NW A : Nat), nwValid NW = true →
        (∀ s < 4096, CFSG.KC.Benes.nwInv NW s =
          if s < 4060 then (unpack 4060 12 A)[s]! else s) →
        (∀ s < 4060, (unpack 4060 12 A)[s]! < 4060) →
        (∀ p, (applyNW NW 1 (x >>> 4096)).testBit p = true ↔
          p ∈ imgSorted (unpack 4060 12 A) ruTreeSets[plK c >>> 4]!) ∧
        ∀ p ∈ imgSorted (unpack 4060 12 A) ruTreeSets[plK c >>> 4]!, p < 4060 := by
      intro NW A hv hg hg'
      have hm : ∀ p, p ∈ imgSorted (unpack 4060 12 A) ruTreeSets[plK c >>> 4]! ↔
          ∃ q, q ∈ ruTreeSets[plK c >>> 4]! ∧ (unpack 4060 12 A)[q]! = p := by
        intro p
        rw [imgSorted, List.mem_mergeSort, List.mem_map]
      refine ⟨fun p => ?_, fun p hp => ?_⟩
      · rw [hm]
        exact applyNW_img hv hg hg' hx2 hx1 p
      · obtain ⟨q, hq, rfl⟩ := (hm p).1 hp
        exact hg' q (hx2 q hq)
    unfold mvU
    rw [hbit2, hgen _ h4]
    by_cases hl : plK c % 16 = 1
    · simp only [hl, ↓reduceIte]
      exact himg _ _ nw1 g1 g1'
    · simp only [hl, ↓reduceIte]
      exact himg _ _ nw0 g0 g0'
  have hroot : ∀ r < 593775, cutK RuTD.FC r = true →
      rootK RuTD.NW0 RuTD.NW1 RuTD.F0 plK RuTD.FC RuTD.T RuTD.D 659760 118755 r = true := by
    intro r hr hcut
    have hm := rngK_spec bndMono
    have hex : ∃ k, r < RuTD.BND (k + 1) := ⟨231, by rw [Nat.eq_of_beq_eq_true bndK]; exact hr⟩
    obtain ⟨i, hi, hmin⟩ : ∃ i, r < RuTD.BND (i + 1) ∧ ∀ m < i, ¬ r < RuTD.BND (m + 1) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    have hi232 : i < 232 := by
      refine Nat.lt_of_not_le fun hl => hmin 231 (by omega) ?_
      rw [Nat.eq_of_beq_eq_true bndK]
      exact hr
    have hlo : RuTD.BND i ≤ r := by
      rcases Nat.eq_zero_or_pos i with e | e
      · rw [e, Nat.eq_of_beq_eq_true bnd0]
        exact Nat.zero_le r
      · have := hmin (i - 1) (by omega)
        rw [Nat.sub_add_cancel e] at this
        omega
    have hmono := Nat.le_of_ble_eq_true (hm i (Nat.zero_le i) (by omega))
    have hbi : rngK (RuTD.BND i) (Nat.sub (RuTD.BND (Nat.succ i)) (RuTD.BND i)) (fun r =>
        Bool.rec (motive := fun _ => Bool) true
          (rootK RuTD.NW0 RuTD.NW1 RuTD.F0 plK RuTD.FC RuTD.T RuTD.D 659760 118755 r)
          (cutK RuTD.FC r)) = true := hb i hi232
    have h1 := rngK_spec hbi r hlo (by
      change r < RuTD.BND i + (RuTD.BND (i + 1) - RuTD.BND i)
      omega)
    rw [hcut] at h1
    exact h1
  have hpart : ∀ j < 593775, partK RuTD.FC j = true := by
    intro j hj
    have h1 := rngK_spec (hp (j / 4096) (by omega)) j
      (by change 4096 * (j / 4096) ≤ j; exact Nat.mul_div_le j 4096)
      (by change j < 4096 * (j / 4096) + 4096; have := Nat.lt_mul_div_succ j (show 0 < 4096 by decide); omega)
    rcases orB_iff'.1 h1 with h2 | h2
    · have : Nat.blt j 593775 = true := Nat.blt_eq.mpr hj
      rw [this] at h2
      exact absurd h2 (by decide)
    · exact h2
  have V := visit_sound (G := Good) hG0 hstep (Nat.eq_of_beq_eq_true fc0)
    (Nat.eq_of_beq_eq_true fcN) hpart cut0 hroot
  have hdist : ∀ i j, i < 593775 → j < 593775 → ruTreeSets[i]! = ruTreeSets[j]! → i = j := by
    intro i j hi hj e
    obtain ⟨-, x, ⟨hx1, -⟩, f, hv⟩ := V i hi
    obtain ⟨-, y, ⟨hy1, -⟩, f', hv'⟩ := V j hj
    refine chk_inj (visitK_succ hv).1 (visitK_succ hv').1 (Nat.eq_of_testBit_eq fun p => ?_)
    apply Bool.eq_iff_iff.2
    rw [hx1, hy1, e]
  refine ⟨?_, hsz, fun j h1 h2 => ?_, ?_, sorted_strict (fun i j hi hj e => hdist i j
    (by rw [hsz] at hi; exact hi) (by rw [hsz] at hj; exact hj) e)⟩
  · rw [hfix, ← lenK_eq]
    exact Nat.eq_of_beq_eq_true fix92
  · obtain ⟨hab, -⟩ := V j h2
    rw [(pl_spec h1 h2).1, (pl_spec h1 h2).2, ← shr4]
    exact hab h1
  · unfold translatesOK
    simp only [hsz, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨by decide, hs0⟩, allLt_of fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with e | e
    · subst e
      rfl
    · obtain ⟨hab, -⟩ := V k hk
      have a' := (hab e).1
      have b' := (hab e).2
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
      refine Or.inr ⟨⟨by rw [hpar k e hk]; exact a', by rw [hlab k e hk]; exact b'⟩, ?_⟩
      exact hsj k e hk (by rw [hpar k e hk]; exact a')

end CertificateChecks.KernelSporSch.Ru2259

end
