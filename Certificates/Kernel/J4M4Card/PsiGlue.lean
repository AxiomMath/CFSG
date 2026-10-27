module

public import Certificates.Kernel.J4M4Card.PsiChain
public import CFSG.Certificates.Kernel.J4M4Card.PsiSound
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Quasithin.Recognition.CertChain
import CFSG.Certificates.Kernel.Misc.ConjTree
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4Card

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KD.J4M4Card CFSG.KS.J4M4Card CFSG.Quasithin.J4M4Card
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3.Native (wordsArr)

theorem arr_get7256 {α : Type} [Inhabited α] {N i : ℕ} (f : ℕ → α) (h : i < N) :
    ((List.range N).map f).toArray[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using h)]
  simp

theorem ofFn_get7256 {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem extract_get7256 {α : Type} [Inhabited α] {a : Array α} {k i : ℕ} (hi : i < k)
    (hk : k ≤ a.size) : (a.extract 0 k)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos a i (by omega), Array.getElem_extract]
  simp

theorem append_get7256 {a b : Array (Array ℕ)} {j : ℕ} (hj : j < a.size) : (a ++ b)[j]! = a[j]! := by
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_append_left hj, getElem!_pos a j hj]

theorem append_get_right7256 {a b : Array (Array ℕ)} {j : ℕ} (h1 : a.size ≤ j)
    (h2 : j < a.size + b.size) : (a ++ b)[j]! = b[j - a.size]! := by
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_append_right h1,
    getElem!_pos b _ (by omega)]

theorem arr_eq7256 {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : t.size = n) (hu : u.size = n) (hgt : CFSG.Monster.B.Co2.Rep n t g) (hgu : CFSG.Monster.B.Co2.Rep n u g) : t = u := by
  apply Array.ext
  · rw [ht, hu]
  · intro i h1 h2
    have hi : i < n := by rwa [ht] at h1
    rw [← getElem!_pos t i h1, ← getElem!_pos u i h2, hgt.apply hi, hgu.apply hi]

theorem unpack_get7256 {n w P i : ℕ} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem wordA_size7256 (n : ℕ) (S Sinv : Array (Array ℕ)) (wd : List ℤ) :
    (wordA n S Sinv wd).size = n := by
  cases wd <;> simp [wordA, idA, compA]

theorem eqA_self7256 (t : Array ℕ) : eqA 2048 t t = true :=
  allLt_iff.2 fun _ _ => beq_self_eq_true _

theorem perm_of_head {n w kS kO nb BP : ℕ} {PS PSI : ℕ → ℕ} {D : List (List ℤ)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact hh.2.2.2.2.1

theorem der_of_head {n w kS kO nb BP : ℕ} {PS PSI : ℕ → ℕ} {D : List (List ℤ)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) {j : ℕ}
    (h1 : kO ≤ j) (h2 : j < kS) :
    PS j = wordK n w (mask w) (pidn n w) PS PSI (D.getD (j - kO) []) := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  have hd := Orb.allN_iff.1 hh.2.2.2.2.2.1 j h2
  rw [Orb.bIf_eq, if_neg (by rw [Orb.blt_dec, decide_eq_true_iff]; omega), Orb.strictB_eq,
    Bool.and_eq_true, Orb.beq_dec, decide_eq_true_iff, Orb.dword_eq h1] at hd
  exact hd.2

theorem perm2 : allN 71 (fun j => permOK 2048 12 (mask 12) (2048 * 12) (P2.S j) (P2.SI j)) = true :=
  perm_of_head P2.head

theorem perm1 : allN 21 (fun j => permOK 128 8 (mask 8) (128 * 8) (P1.S j) (P1.SI j)) = true :=
  perm_of_head P1.head

theorem psiOrig_size : (psiOrig ()).size = 62 := by simp [psiOrig]

theorem psiS_size : (psiS ()).size = 71 := by simp [psiS, psiOrig]

theorem psiOrig_get {j : ℕ} (hj : j < 62) : (psiOrig ())[j]! = psiArr j := by
  unfold psiOrig
  exact arr_get7256 _ hj

theorem psiS_lt {j : ℕ} (hj : j < 62) : (psiS ())[j]! = psiArr j := by
  unfold psiS
  rw [append_get7256 (by rw [psiOrig_size]; exact hj), psiOrig_get hj]

theorem psiS_ge {j : ℕ} (h1 : 62 ≤ j) (h2 : j < 71) :
    (psiS ())[j]! = wordA 2048 (psiOrig ()) (rawInvs 2048 (psiOrig ())) (psiW.getD j []) := by
  unfold psiS
  rw [append_get_right7256 (by rw [psiOrig_size]; exact h1) (by simp [psiOrig_size]; omega),
    psiOrig_size, arr_get7256 _ (by omega), Nat.add_sub_cancel' h1]

theorem arr_ext7256 {n : ℕ} {t u : Array ℕ} (ht : t.size = n) (hu : u.size = n)
    (h : ∀ i < n, t[i]! = u[i]!) : t = u := by
  apply Array.ext
  · rw [ht, hu]
  · intro i h1 h2
    rw [← getElem!_pos t i h1, ← getElem!_pos u i h2]
    exact h i (by omega)

theorem psiArr_get {j i : ℕ} (hi : i < 2048) : (psiArr j)[i]! = xorMasks (maskTab.getD j []) i := by
  unfold psiArr
  exact ofFn_get7256 (fun c : Fin 2048 => xorMasks (maskTab.getD j []) c) hi

theorem psiArr_eq {j : ℕ} (hj : j < 62) : psiArr j = unpack 2048 12 (P2.S j) := by
  refine arr_ext7256 (n := 2048) (by simp [psiArr]) (by simp [unpack]) fun i hi => ?_
  rw [psiArr_get hi, unpack_get7256 hi, laneK_spec lane_ok (Nat.zero_le j) (by omega) i hi]

theorem rep2 {h : ℕ} (hh : h < 71) :
    CFSG.Monster.B.Co2.Rep 2048 (unpack 2048 12 (P2.S h)) (permOfArr 2048 (unpack 2048 12 (P2.S h))) ∧
      CFSG.Monster.B.Co2.Rep 2048 (unpack 2048 12 (P2.SI h)) (permOfArr 2048 (unpack 2048 12 (P2.S h)))⁻¹ :=
  rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 perm2 h hh))

theorem psiS_der {j : ℕ} (h1 : 62 ≤ j) (h2 : j < 71) : (psiS ())[j]! = unpack 2048 12 (P2.S j) := by
  rw [psiS_ge h1 h2]
  have hl : lettersK 62 (psiW.getD j []) = true := by interval_cases j <;> decide
  obtain ⟨hP, hlo⟩ := Orb.prep_wordK
    (gs := fun h => permOfArr 2048 (unpack 2048 12 (P2.S h))) (j := 62) (by norm_num)
    (by norm_num) (fun h hh => Orb.prep_of_rep (rep2 (by omega)).1)
    (fun h hh => Orb.prep_of_rep (rep2 (by omega)).2) _ hl
  have hS' : ∀ h < 62, CFSG.Monster.B.Co2.Rep 2048 (psiOrig ())[h]! (permOfArr 2048 (unpack 2048 12 (P2.S h))) :=
    fun h hh => by
      rw [psiOrig_get hh, psiArr_eq hh]
      exact (rep2 (by omega)).1
  have hSi : ∀ h < 62, CFSG.Monster.B.Co2.Rep 2048 (rawInvs 2048 (psiOrig ()))[h]!
      (permOfArr 2048 (unpack 2048 12 (P2.S h)))⁻¹ := fun h hh => by
    rw [Orb.rawInvs_get (by rw [psiOrig_size]; exact hh)]
    exact rep_invCand (hS' h hh)
  have hrW := rep_wordA hS' hSi _ hlo
  have he := der_of_head P2.head h1 h2
  have hw : psiD.getD (j - 62) [] = psiW.getD j [] := by interval_cases j <;> rfl
  rw [hw] at he
  have hrP : CFSG.Monster.B.Co2.Rep 2048 (unpack 2048 12 (P2.S j)) (Quiver.SchreierGraph.evalWord
      (fun h : Fin 62 => permOfArr 2048 (unpack 2048 12 (P2.S h))) (toLetters 62 (psiW.getD j []))) := by
    rw [he]
    exact Orb.rep_unpack hP
  exact arr_eq7256 (wordA_size7256 _ _ _ _) (by simp [unpack]) hrW hrP

theorem binds2 : Binds 2048 12 P2.S 71 4 P2.BP (psiS ()) psiBase.toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, psiS_size, fun j hj => ?_, rfl, fun t ht => ?_⟩
  · rcases Nat.lt_or_ge j 62 with h | h
    · rw [psiS_lt h, psiArr_eq h]
    · exact psiS_der h hj
  · interval_cases t <;> decide

theorem orb2 : rawOrbitSizes 2048 (psiS ()) psiBase.toArray = [120, 84, 16, 2] := by
  rw [rawOrbitSizesK_sound binds2 perm2 P2.hl]
  exact orb2_ok

@[expose] noncomputable def S128 : Array (Array ℕ) :=
  ((List.range 21).map fun t => unpack 128 8 (P1.S t)).toArray

@[expose] def base128 : List (Fin 128) := [0, 1, 2]

theorem S128_get {t : ℕ} (ht : t < 21) : S128[t]! = unpack 128 8 (P1.S t) := arr_get7256 _ ht

theorem binds1 : Binds 128 8 P1.S 21 3 P1.BP S128 (base128.map Fin.val).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [S128], fun j hj => S128_get hj, rfl,
    fun t ht => ?_⟩
  interval_cases t <;> decide

theorem raw1 : rawChainOK 128 (S128.extract 0 17) S128 (base128.map Fin.val).toArray
    (wordsArr 17 21 psiD128) 1 = true :=
  rawChainK_sound (NS := 1) (CH := 128) binds1 P1.head P1.hl (by norm_num) P1.hs

theorem S128_extract_size : (S128.extract 0 17).size = 17 := by simp [S128]

theorem card1 : Nat.card (Subgroup.closure {g | ∃ k < (S128.extract 0 17).size,
    permOfArr 128 (S128.extract 0 17)[k]! = g}) = 322560 := by
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 128) (O := S128.extract 0 17) (S := S128)
    (base := base128) (W := wordsArr 17 21 psiD128) (chunks := 1) (by norm_num) (by decide)
    (by norm_num) (by rw [S128_extract_size]; simp [S128])
    (fun i hi => (extract_get7256 (S128_extract_size ▸ hi) (by simp [S128])).symm)
    (by rw [S128_extract_size]; exact raw1)
  rw [h, rawOrbitSizesK_sound binds1 perm1 P1.hl]
  exact orb1_ok

theorem rep1 {t : ℕ} (ht : t < 21) :
    CFSG.Monster.B.Co2.Rep 128 S128[t]! (permOfArr 128 S128[t]!) := by
  rw [S128_get ht]
  exact (rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 perm1 t ht))).1

theorem repS {j : ℕ} (hj : j < 62) : CFSG.Monster.B.Co2.Rep 2048 (psiS ())[j]! (permOfArr 2048 (psiS ())[j]!) := by
  rw [psiS_lt hj, psiArr_eq hj]
  exact (rep2 (by omega)).1

theorem sigma_val {j : ℕ} (hj : j < 62) (x : Fin 2048) :
    (permOfArr 2048 (psiS ())[j]! x).val = pg 12 (mask 12) (P2.S j) x.val := by
  rw [← (repS hj).apply x.isLt, psiS_lt hj, psiArr_eq hj, unpack_get7256 x.isLt]

theorem rx_lt {j : ℕ} (hj : j < 62) : psiRx j < 17 := lt_of_blt7256 (Orb.allN_iff.1 rx_ok j hj)

theorem tau_val {j : ℕ} (hj : j < 62) (k : Fin 128) :
    (permOfArr 128 S128[psiRx j]! k).val = pg 8 (mask 8) (P1.S (psiRx j)) k.val := by
  have ht : psiRx j < 21 := by have := rx_lt hj; omega
  rw [← (rep1 ht).apply k.isLt, S128_get ht, unpack_get7256 k.isLt]

theorem card_psi_le : Nat.card (Subgroup.closure (Set.range fun j : Fin 62 =>
    permOfArr 2048 (psiS ())[j.val]!)) ≤ (rawOrbitSizes 2048 (psiS ()) psiBase.toArray).prod := by
  rw [orb2]
  have hle := card_le_of_pairs (σ := fun j : Fin 62 => permOfArr 2048 (psiS ())[j.val]!)
    (τ := fun j : Fin 62 => permOfArr 128 S128[psiRx j.val]!) (oFin ov_ok)
    (fun j a b c hc => by
      have hj : j.val < 0 + 62 := by have := j.isLt; omega
      beta_reduce
      rw [sigma_val j.isLt, sigma_val j.isLt, sigma_val j.isLt, hc,
        laneK_spec lane_ok (Nat.zero_le _) hj _ (xor_lt2048 a b),
        laneK_spec lane_ok (Nat.zero_le _) hj _ a.isLt,
        laneK_spec lane_ok (Nat.zero_le _) hj _ b.isLt, xorMasks_xor])
    (fun j k => Fin.ext (by
      beta_reduce
      rw [sigma_val j.isLt]
      change pg 12 (mask 12) (P2.S j.val) (psiOv k.val) = psiOv (permOfArr 128 S128[psiRx j.val]! k).val
      rw [tau_val j.isLt]
      exact Nat.eq_of_beq_eq_true (Orb.allN_iff.1 (Orb.allN_iff.1 pair_ok j.val j.isLt) k.val k.isLt)))
    (fun ρ hρ hfix => eq_one_of_fix ov_ok span_ok hρ hfix)
  have hsub : Subgroup.closure (Set.range fun j : Fin 62 => permOfArr 128 S128[psiRx j.val]!) ≤
      Subgroup.closure {g | ∃ k < (S128.extract 0 17).size,
        permOfArr 128 (S128.extract 0 17)[k]! = g} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_closure ⟨psiRx j.val, by rw [S128_extract_size]; exact rx_lt j.isLt,
      by rw [extract_get7256 (rx_lt j.isLt) (by simp [S128])]⟩
  have h2 := Subgroup.card_le_of_le hsub
  rw [card1] at h2
  have e : ([120, 84, 16, 2] : List ℕ).prod = 322560 := by norm_num
  rw [e]
  exact le_trans hle h2

theorem chkPsi_ok : chkPsi () = true := by
  have hc := rawChainK_of_card (chunks := 1) binds2 P2.head P2.hl card_psi_le
  have hc' : rawChainOK 2048 ((psiS ()).extract 0 62) (psiS ()) psiBase.toArray psiW 1 = true := by
    rw [CFSG.KC.Misc.ConjTree.rawChainOK_congrW (W' := wordsArr 62 71 psiD)
      (by rw [wordsArr, Array.size_ofFn]; rfl) (fun j h1 h2 => by
        have h1' : 62 ≤ j := by simp [psiS_size] at h1; omega
        have h2' : j < 71 := by rw [psiS_size] at h2; exact h2
        interval_cases j <;> rfl)]
    exact hc
  unfold chkPsi
  rw [hc', orb2]
  simp only [Bool.true_and, beq_self_eq_true]
  rw [List.all_eq_true]
  intro i hi
  rw [psiS_lt (List.mem_range.1 hi)]
  exact eqA_self7256 _

end CertificateChecks.KernelJ4M4Card

end
