module

public import Certificates.Kernel.Sporadic.OddCore.Suz2308R
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Spor.RowWordSound
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Sporadic.SuzOddCore.GraphArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Sort
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.S2308

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.KC.Enum CFSG.KS
open CFSG.KS.Row CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw CFSG.KS.Mathieu CFSG.PSL3Four.Native
open CFSG.Certificates.Native CertificateChecks.KernelSpor

theorem allR_spec {lo len : Nat} {f : Nat → Bool} (h : allR lo len f = true) :
    ∀ i, lo ≤ i → i < lo + len → f i = true := by
  intro i h1 h2
  have h' := allN_spec h (i - lo) (by omega)
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rwa [e] at h'

theorem qtr_all {f : Nat → Bool} (h0 : qtr f 0 = true) (h1 : qtr f 1 = true)
    (h2 : qtr f 2 = true) (h3 : qtr f 3 = true) : ∀ x < 22880, f x = true := by
  intro x hx
  unfold qtr at h0 h1 h2 h3
  simp only [Nat.mul_eq] at h0 h1 h2 h3
  rcases Nat.lt_or_ge x 5720 with a | a
  · exact allR_spec h0 x (by omega) (by omega)
  rcases Nat.lt_or_ge x 11440 with b | b
  · exact allR_spec h1 x (by omega) (by omega)
  rcases Nat.lt_or_ge x 17160 with c | c
  · exact allR_spec h2 x (by omega) (by omega)
  · exact allR_spec h3 x (by omega) (by omega)

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) : nIf(c, t, e) = if c then t else e := by cases c <;> rfl

theorem o2_eq (f g : Nat → Nat) (x : Nat) : o2 f g x = f (g x) := strictN_app _ _

theorem itr_succ (f : Nat → Nat) (k x : Nat) : itr f (k + 1) x = f (itr f k x) :=
  strictN_app _ _

theorem itr_zero (f : Nat → Nat) (x : Nat) : itr f 0 x = x := rfl

theorem itr_congr {f g : Nat → Nat} (hfg : ∀ y < 22880, f y = g y) (hf : ∀ y < 22880, f y < 22880) :
    ∀ k, ∀ x < 22880, itr f k x = itr g k x ∧ itr f k x < 22880
  | 0, x, hx => ⟨rfl, hx⟩
  | k + 1, x, hx => by
    obtain ⟨e, hl⟩ := itr_congr hfg hf k x hx
    rw [itr_succ, itr_succ, ← e, hfg _ hl]
    exact ⟨rfl, by rw [← hfg _ hl]; exact hf _ hl⟩

theorem cntK_eq (n : Nat) (p : Nat → Bool) : cntK n p = ((List.range n).filter p).length := by
  unfold cntK
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  generalize List.range n = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases h : p a <;> simp [h, nIf_eq]

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · rw [beq_eq_false_iff_ne]
    intro e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  · rw [Nat.eq_of_beq_eq_true h]
    exact beq_self_eq_true _

theorem alt_iff {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ i < n, p i = true :=
  CFSG.Monster.B.Co2.allLt_iff

theorem comp_eqA (n : Nat) (p q : Array Nat) : comp n p q = compA n p q := rfl

theorem eqA_true {n : Nat} {t u : Array Nat} (h : ∀ x < n, t[x]! = u[x]!) : eqA n t u = true :=
  alt_iff.2 fun i hi => beq_iff_eq.2 (h i hi)

theorem eqA_false {n x : Nat} {t u : Array Nat} (hx : x < n) (h : t[x]! ≠ u[x]!) :
    eqA n t u = false := by
  cases e : eqA n t u
  · rfl
  · exact absurd (beq_iff_eq.1 (alt_iff.1 e x hx)) h

theorem arr_eq {n : Nat} {t u : Array Nat} (ht : t.size = n) (hu : u.size = n)
    (h : ∀ x < n, t[x]! = u[x]!) : t = u := by
  apply Array.ext
  · rw [ht, hu]
  · intro i h1 h2
    rw [← getElem!_pos t i h1, ← getElem!_pos u i h2]
    exact h i (by omega)

theorem size_wordA (n : Nat) (S Sinv : Array (Array Nat)) (w : List Int) :
    (wordA n S Sinv w).size = n := by
  cases w <;> simp [wordA, compA, idA]

theorem map_get {L : Array (Array Nat)} {f : Array Nat → Array Nat} {j : Nat} (hj : j < L.size) :
    (L.map f)[j]! = f L[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos L j hj]

theorem rl_get {F : Nat → Nat} {o x : Nat} (hx : x < 22880) :
    (rowArr 22880 15 F o)[x]! = rl F o x := rowArr_get hx

theorem rowArr_congr {F F' : Nat → Nat} {o o' : Nat} (h : ∀ r < 715, F (o + r) = F' (o' + r)) :
    rowArr 22880 15 F o = rowArr 22880 15 F' o' := by
  refine arr_eq (size_rowArr _ _ _ _) (size_rowArr _ _ _ _) fun x hx => ?_
  rw [rowArr_get hx, rowArr_get hx]
  unfold rg
  have hr : Nat.shiftRight x 5 < 715 := by
    change x >>> 5 < 715
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e := h _ hr
  simp only [Nat.add_eq] at e ⊢
  rw [e]

theorem cert_get {k x : Nat} (hk : k < 12) (hx : x < 22880) : (certArr k)[x]! = cgk k x := by
  rw [certArr_eq hk, rowArr_get hx]
  rfl

theorem cert_inv {k : Nat} (hk : k < 12) :
    invCand 22880 (certArr k) = rowArr 22880 15 SuzCertI (ofs k) := by
  rw [certArr_eq hk]
  exact (rpermK_sound (allN_spec cert_perms k hk)).1

theorem cert_rngF {k : Nat} (hk : k < 12) : ∀ i < 22880, rg 15 (mask 15) SuzCertT.F (ofs k) i < 22880 :=
  rpermK_range (allN_spec cert_perms k hk)

theorem cert_rngG {k : Nat} (hk : k < 12) : ∀ i < 22880, rg 15 (mask 15) SuzCertI (ofs k) i < 22880 :=
  rpermK_range (allN_spec crev k hk)

theorem strong_get {j : Nat} (hj : j < 10) : certStrongArrs[j]! = certArr (j + 2) := by
  interval_cases j <;> simp [certStrongArrs]

theorem strongInv_get {j : Nat} (hj : j < 10) :
    certStrongInvs[j]! = rowArr 22880 15 SuzCertI (ocs j) := by
  have e : certStrongInvs[j]! = invCand 22880 certStrongArrs[j]! := by
    interval_cases j <;> simp [certStrongInvs, certStrongArrs]
  rw [e, strong_get hj, cert_inv (k := j + 2) (by omega)]
  rfl

theorem strong_rows {j : Nat} (hj : j < 10) :
    certStrongArrs[j]! = rowArr 22880 15 SuzCertT.F (ocs j) := by
  rw [strong_get hj, certArr_eq (k := j + 2) (by omega)]
  rfl

theorem cen_get {r x : Nat} (hr : r < 9) (hx : x < 22880) : (centerFull r)[x]! = cf r x := by
  rw [centerFull_eq hr, rowArr_get hx]
  rfl

theorem cen_lt {r x : Nat} (hr : r < 9) (hx : x < 22880) : cf r x < 22880 :=
  rpermK_range (allN_spec full_perms r hr) x hx

theorem cen_perm {r : Nat} (hr : r < 9) :
    CFSG.Sporadic.SuzOddCore.permOK 22880 (centerFull r) = true := by
  have hp := rpermK_sound (n := 22880) (w := 15) (o := 715 * r) (o' := 715 * r)
    (allN_spec full_perms r hr)
  unfold CFSG.Sporadic.SuzOddCore.permOK
  rw [centerFull_eq hr, size_rowArr, hp.1]
  simp only [beq_self_eq_true, Bool.true_and]
  exact hp.2

@[expose] noncomputable def FR (j : Nat) : Array Nat := rowArr 22880 15 S2308FX (ofs j)

theorem FR_get {j x : Nat} (hx : x < 22880) : (FR j)[x]! = fx j x := rowArr_get hx

theorem FR_base {j : Nat} (hj : j < 8) : FR j = certArr (j + 4) := by
  rw [certArr_eq (k := j + 4) (by omega)]
  unfold FR
  apply rowArr_congr
  intro r hr
  exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec fbase j hj) r hr)

theorem F_inv {j : Nat} (hj : j < 14) :
    invCand 22880 (FR j) = rowArr 22880 15 S2308FXI (ofs j) ∧
      isInvA 22880 (FR j) (rowArr 22880 15 S2308FXI (ofs j)) = true :=
  rpermK_sound (allN_spec fperm j hj)

theorem wordF {kS : Nat} (hk : kS ≤ 14) {L : Array (Array Nat)} (hs : L.size = kS)
    (hL : ∀ j < kS, L[j]! = FR j) {wd : List Int} (hl : lettersOK kS wd = true) :
    ∀ x < 22880, (wordA 22880 L (L.map (invCand 22880)) wd)[x]! = wpF wd x ∧ wpF wd x < 22880 :=
  rwordPt_eq (kS := kS) (O := ofs) (fun j hj => hL j hj)
    (fun j hj => by rw [map_get (L := L) (j := j) (by omega), hL j hj, (F_inv (j := j) (by omega)).1])
    (fun j hj => rpermK_range (allN_spec fperm j (by omega)))
    (fun j hj => rpermK_range (allN_spec fpermR j (by omega))) wd hl

theorem fd_all {k : Nat} (hk : k < 6) : ∀ x < 22880, fdP k x = true := by
  interval_cases k
  exacts [allN_spec fd0, allN_spec fd1, allN_spec fd2, allN_spec fd3, allN_spec fd4, allN_spec fd5]

theorem fullExt_get : ∀ k ≤ 6, (fullExtArrList k).size = 8 + k ∧
    ∀ j < 8 + k, (fullExtArrList k)[j]! = FR j
  | 0, _ => by
    refine ⟨by simp [fullExtArrList, localStrongIdx], fun j hj => ?_⟩
    rw [FR_base hj]
    interval_cases j <;> simp [fullExtArrList, localStrongIdx, certStrongArrs]
  | k + 1, hk => by
    obtain ⟨hs, hg⟩ := fullExt_get k (by omega)
    have hl : lettersOK (8 + k) (localDerivs.getD (8 + k) []) = true := by
      have : k < 6 := by omega
      interval_cases k <;> decide
    have hpush : fullExtArrList (k + 1) = (fullExtArrList k).push
        (wordA 22880 (fullExtArrList k) ((fullExtArrList k).map (invCand 22880))
          (localDerivs.getD (8 + k) [])) := rfl
    rw [hpush]
    refine ⟨by simp [hs]; omega, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j (8 + k) with h | h
    · have e1 : ∀ (A : Array (Array Nat)) (W : Array Nat), A.size = 8 + k →
          (A.push W)[j]! = A[j]! := by
        intro A W hA
        rw [getElem!_pos _ j (by simp; omega), getElem!_pos A j (by omega)]
        exact Array.getElem_push_lt (by omega)
      rw [e1 _ _ hs, hg j h]
    · have hj' : j = 8 + k := by omega
      subst hj'
      have ep : ∀ (A : Array (Array Nat)) (W : Array Nat), A.size = 8 + k → (A.push W)[8 + k]! = W := by
        intro A W hA
        rw [← hA]
        simp
      rw [ep _ _ hs]
      refine arr_eq (size_wordA _ _ _ _) (size_rowArr _ _ _ _) fun x hx => ?_
      rw [(wordF (kS := 8 + k) (by omega) hs hg hl x hx).1, FR_get hx]
      exact (Nat.eq_of_beq_eq_true (fd_all (by omega) x hx)).symm

theorem full_size : fullExtArrs.size = 14 := (fullExt_get 6 le_rfl).1

theorem full_get {j : Nat} (hj : j < 14) : fullExtArrs[j]! = FR j := (fullExt_get 6 le_rfl).2 j hj

@[expose] noncomputable def TR (a : Nat) : Array Nat := rowArr 22880 15 S2308TX (ofs a)

theorem tw_all {a : Nat} (ha : a < 5) : ∀ x < 22880, twP a x = true := by
  interval_cases a
  exacts [qtr_all tw0q0 tw0q1 tw0q2 tw0q3, qtr_all tw1q0 tw1q1 tw1q2 tw1q3,
    qtr_all tw2q0 tw2q1 tw2q2 tw2q3, qtr_all tw3q0 tw3q1 tw3q2 tw3q3,
    qtr_all tw4q0 tw4q1 tw4q2 tw4q3]

theorem T_get {a : Nat} (ha : a < 5) : (tFullOf fullExtArrs)[a]! = TR a := by
  rw [tFullOf, getElem!_pos _ a (by simp; omega), Array.getElem_ofFn]
  have hl : lettersOK 14 (sylowQuotWords.getD a []) = true := by
    interval_cases a <;> decide
  refine arr_eq (size_wordA _ _ _ _) (size_rowArr _ _ _ _) fun x hx => ?_
  rw [(wordF le_rfl full_size (fun j hj => full_get hj) hl x hx).1, TR, rowArr_get hx]
  exact (Nat.eq_of_beq_eq_true (tw_all ha x hx)).symm

theorem T_size : (tFullOf fullExtArrs).size = 5 := by simp [tFullOf]

theorem tx_lt {a x : Nat} (ha : a < 5) (hx : x < 22880) : tx a x < 22880 := by
  have hl : lettersOK 14 (sylowQuotWords.getD a []) = true := by
    interval_cases a <;> decide
  rw [Nat.eq_of_beq_eq_true (tw_all ha x hx)]
  exact (wordF le_rfl full_size (fun j hj => full_get hj) hl x hx).2

theorem z_all : ∀ x < 22880, zP x = true := qtr_all zq0 zq1 zq2 zq3

theorem zP_facts {x : Nat} (hx : x < 22880) : wx x = wpS zWord x ∧ zx x = itr wx 7 x ∧
    itr zx 3 x = x ∧ ∀ j < 8, o2 (cgk (Nat.add j 4)) (o2 zx (ci (Nat.add j 4))) x =
      nIf(Nat.beq (nget S2308W (Nat.add 82 j)) 0, zx x, o2 zx zx x) := by
  have h := z_all x hx
  unfold zP at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec h4 j hj)⟩

theorem wS {x : Nat} (hx : x < 22880) :
    (wordA 22880 certStrongArrs certStrongInvs zWord)[x]! = wx x ∧ wx x < 22880 := by
  have h := rwordPt_eq (kS := 10) (O := ocs) (F := SuzCertT.F) (G := SuzCertI)
    (fun j hj => strong_rows hj) (fun j hj => strongInv_get hj)
    (fun j hj => cert_rngF (k := j + 2) (by omega)) (fun j hj => cert_rngG (k := j + 2) (by omega))
    zWord (by decide) x hx
  rw [(zP_facts hx).1]
  exact h

theorem z_get {x : Nat} (hx : x < 22880) : zArr[x]! = zx x ∧ zx x < 22880 := by
  have hw : ∀ y < 22880, (wordA 22880 certStrongArrs certStrongInvs zWord)[y]! < 22880 :=
    fun y hy => by rw [(wS hy).1]; exact (wS hy).2
  have hp : ∀ k, ∀ y < 22880, (powArr 22880 (wordA 22880 certStrongArrs certStrongInvs zWord) k)[y]! =
      itr (fun v => (wordA 22880 certStrongArrs certStrongInvs zWord)[v]!) k y := by
    intro k
    induction k with
    | zero => intro y hy; rw [powArr, idA_get hy]; rfl
    | succ k ih =>
      intro y hy
      rw [powArr, compA_get hy, ih y hy, itr_succ]
  have hc := itr_congr (fun y hy => (wS hy).1) hw 7 x hx
  have e7 : zPower = 7 := rfl
  unfold zArr
  rw [e7, hp 7 x hx, hc.1, ← (zP_facts hx).2.1]
  refine ⟨rfl, ?_⟩
  rw [(zP_facts hx).2.1, ← hc.1]
  exact hc.2

theorem compA3 {t : Array Nat} {f : Nat → Nat} (ht : ∀ y < 22880, t[y]! = f y)
    (hf : ∀ y < 22880, f y < 22880) {x : Nat} (hx : x < 22880) :
    (compA 22880 t (compA 22880 t t))[x]! = itr f 3 x := by
  rw [compA_get hx, compA_get hx, ht x hx, ht _ (hf x hx), ht _ (hf _ (hf x hx)), itr_succ,
    itr_succ, itr_succ, itr_zero]

theorem ld_eq {i : Nat} (hi : i < 280) (h : i < localDomain.length) : localDomain[i] = ld i := by
  simp only [localDomain_eq, Array.getElem_toList]
  rw [← getElem!_pos _ i (by simpa [unpack] using hi), CFSG.KS.Raw.Orb.unpack_get hi]
  rfl

theorem dom_len : localDomain.length = 280 := domain.1

theorem pw_of_strictIncr : ∀ l : List Nat, strictIncr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictIncr, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pw_of_strictIncr (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem dom_pw : localDomain.Pairwise (· < ·) := pw_of_strictIncr _ domain.2.1

theorem dom_nodup : localDomain.Nodup := dom_pw.imp (fun h => Nat.ne_of_lt h)

theorem rst_facts : (∀ j < 14, ∀ i < 280, fx j (ld i) = ld (pg 9 (mask 9) (SuzLocR (Nat.add 8 j)) i)) ∧
    (∀ a < 5, ∀ i < 280, tx a (ld i) = ld (pg 9 (mask 9) (S2308CE.G a) i)) ∧
    (∀ i < 280, cf 3 (ld i) = ld (pg 9 (mask 9) (SuzCenC 3) i)) ∧
    (∀ i < 280, ld i ≠ 0 ∧ zx (ld i) = ld i) ∧
    (∀ k < 8, SuzLocR k = SuzLocR (Nat.add 8 k)) ∧
    (∀ j < 14, S2308LC.S j = SuzLocR (Nat.add 8 j)) ∧
    (∀ t < 4, nget [0, 1, 2, 3] t = pg 9 (mask 9) S2308LC.BP t) := by
  have h := rst
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun j hj i hi => Nat.eq_of_beq_eq_true (allN_spec (allN_spec h1 j hj) i hi),
    fun a ha i hi => Nat.eq_of_beq_eq_true (allN_spec (allN_spec h2 a ha) i hi),
    fun i hi => Nat.eq_of_beq_eq_true (allN_spec h3 i hi), fun i hi => ?_,
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h5 k hk),
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec h6 j hj),
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec h7 t ht)⟩
  have e := allN_spec h4 i hi
  simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at e
  refine ⟨fun h0 => ?_, Nat.eq_of_beq_eq_true e.2⟩
  rw [h0] at e
  exact absurd e.1 (by decide)

theorem ld_lt {i : Nat} (hi : i < 280) : ld i < 22880 := by
  have := domain.2.2 (localDomain[i]'(by rw [dom_len]; exact hi)) (List.getElem_mem _)
  rwa [ld_eq hi] at this

theorem mem_dom {x : Nat} : x ∈ localDomain ↔ ∃ i < 280, ld i = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [dom_len] at hi; exact hi, (ld_eq (by rw [dom_len] at hi; exact hi) hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [dom_len]; exact hi, ld_eq hi _⟩

theorem delta_eq : deltaOf zArr = localDomain := by
  have hpw : (deltaOf zArr).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hmem : ∀ x, x ∈ deltaOf zArr ↔ x < 22880 ∧ x ≠ 0 ∧ zx x = x := by
    intro x
    unfold deltaOf
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hx, h⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
      exact ⟨hx, h.1, by rw [← (z_get hx).1]; exact h.2⟩
    · rintro ⟨hx, h0, hz⟩
      refine ⟨hx, ?_⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      exact ⟨h0, by rw [(z_get hx).1]; exact hz⟩
  have hsub : localDomain ⊆ deltaOf zArr := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_dom.1 hx
    exact (hmem _).2 ⟨ld_lt hi, (rst_facts.2.2.2.1 i hi).1, (rst_facts.2.2.2.1 i hi).2⟩
  have hlen : (deltaOf zArr).length = 280 := by
    have hc := zpts
    simp only [bAnd_eq, Bool.and_eq_true] at hc
    have hcnt := Nat.eq_of_beq_eq_true hc.2.2.2.1
    rw [cntK_eq] at hcnt
    have hfc : (List.range 22880).filter (fun i => i != 0 && zArr[i]! == i) =
        (List.range 22880).filter (fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i)) := by
      apply List.filter_congr
      intro x hx
      rw [List.mem_range] at hx
      rw [bAnd_eq, notB_eq, (z_get hx).1]
      simp only [bne, beq_nat]
    unfold deltaOf
    rw [hfc]
    exact hcnt
  have hperm := (List.subperm_of_subset dom_nodup hsub).perm_of_length_le
    (by rw [hlen, dom_len])
  exact (List.Subset.antisymm_of_pairwise dom_pw hpw hsub (fun x hx => hperm.symm.subset hx)).symm

theorem conj_case {j : Nat} (hj : j < 8) :
    (eqA 22880 (compA 22880 certStrongArrs[j + 2]! (compA 22880 zArr certStrongInvs[j + 2]!)) zArr ||
      eqA 22880 (compA 22880 certStrongArrs[j + 2]! (compA 22880 zArr certStrongInvs[j + 2]!))
        (compA 22880 zArr zArr)) = true := by
  have hc : ∀ x < 22880, (compA 22880 certStrongArrs[j + 2]!
      (compA 22880 zArr certStrongInvs[j + 2]!))[x]! =
        o2 (cgk (Nat.add j 4)) (o2 zx (ci (Nat.add j 4))) x := by
    intro x hx
    have hy : ci (Nat.add j 4) x < 22880 := cert_rngG (k := j + 4) (by omega) x hx
    rw [compA_get hx, compA_get hx, strongInv_get (j := j + 2) (by omega), rowArr_get hx,
      strong_rows (j := j + 2) (by omega),
      o2_eq, o2_eq]
    have e1 : rg 15 (mask 15) SuzCertI (ocs (j + 2)) x = ci (Nat.add j 4) x := rfl
    rw [e1, (z_get hy).1, rowArr_get (z_get hy).2]
    rfl
  by_cases hf : nget S2308W (Nat.add 82 j) = 0
  · have : eqA 22880 (compA 22880 certStrongArrs[j + 2]! (compA 22880 zArr certStrongInvs[j + 2]!))
        zArr = true := eqA_true fun x hx => by
      rw [hc x hx, (zP_facts hx).2.2.2 j hj, hf, (z_get hx).1]
      rfl
    rw [this, Bool.true_or]
  · have : eqA 22880 (compA 22880 certStrongArrs[j + 2]! (compA 22880 zArr certStrongInvs[j + 2]!))
        (compA 22880 zArr zArr) = true := eqA_true fun x hx => by
      have hb : Nat.beq (nget S2308W (Nat.add 82 j)) 0 = false := by
        cases e : Nat.beq (nget S2308W (Nat.add 82 j)) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hf
      rw [hc x hx, (zP_facts hx).2.2.2 j hj, hb, compA_get hx, (z_get hx).1, (z_get (z_get hx).2).1]
      exact o2_eq _ _ _
    rw [this, Bool.or_true]

theorem zpt_facts : zx 0 = 0 ∧ zx (nget S2308W 0) ≠ nget S2308W 0 ∧ nget S2308W 0 < 22880 := by
  have hc := zpts
  simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at hc
  refine ⟨Nat.eq_of_beq_eq_true hc.1, fun h => ?_, Eq.mp Nat.blt_eq hc.2.2.1⟩
  rw [h, Nat.beq_refl] at hc
  exact absurd hc.2.1 (by decide)

theorem zChecks_ok : zChecks = true := by
  unfold zChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨eqA_true fun x hx => ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [compA3 (fun y hy => (z_get hy).1) (fun y hy => (z_get hy).2) hx, (zP_facts hx).2.2.1,
      idA_get hx]
  · rw [Bool.not_eq_true']
    obtain ⟨-, h1, h2⟩ := zpt_facts
    exact eqA_false h2 (by rw [(z_get h2).1, idA_get h2]; exact h1)
  · rw [(z_get (x := 0) (by norm_num)).1, zpt_facts.1]
    rfl
  · rw [List.all_eq_true]
    intro j hj
    simp only [certStabIdx, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [conj_case (j := 0) (by norm_num), conj_case (j := 1) (by norm_num),
      conj_case (j := 2) (by norm_num), conj_case (j := 3) (by norm_num),
      conj_case (j := 4) (by norm_num), conj_case (j := 5) (by norm_num),
      conj_case (j := 6) (by norm_num), conj_case (j := 7) (by norm_num)]
  · rw [delta_eq]
    exact beq_self_eq_true _

theorem restrict_eq {t : Array Nat} {P : Nat} (h : ∀ i < 280, t[ld i]! = ld (pg 9 (mask 9) P i))
    (hr : ∀ i < 280, pg 9 (mask 9) P i < 280) : restrictArr localDomain t = unpack 280 9 P := by
  refine arr_eq (n := 280) (by simp [restrictArr, dom_len]) (by simp [unpack]) fun i hi => ?_
  rw [CFSG.KS.Raw.Orb.unpack_get hi, getElem!_pos _ i (by simp [restrictArr, dom_len]; exact hi)]
  simp only [restrictArr, List.getElem_toArray, List.getElem_map]
  rw [ld_eq hi, h i hi, ← ld_eq (hr i hi) (by rw [dom_len]; exact hr i hi),
    dom_nodup.idxOf_getElem]

theorem unpack_rng {P Q : Nat} (h : invEqK 280 9 (mask 9) (280 * 9) P Q = true) :
    ∀ i < 280, pg 9 (mask 9) P i < 280 := by
  intro i hi
  have := (isInvA_spec (invEqK_sound h).2 hi).1
  rwa [CFSG.KS.Raw.Orb.unpack_get hi] at this

theorem canon_rng {P : Nat} (h : canonK 280 9 (mask 9) (280 * 9) P = true) :
    ∀ i < 280, pg 9 (mask 9) P i < 280 := fun i hi =>
  Eq.mp Nat.blt_eq (allN_spec (range_of_canonK h) i hi)

theorem loc_get {k : Nat} (hk : k < 22) : localRun k = unpack 280 9 (SuzLocR k) := localRun_eq hk

theorem restrict_F {j : Nat} (hj : j < 14) :
    restrictArr localDomain (FR j) = unpack 280 9 (SuzLocR (Nat.add 8 j)) :=
  restrict_eq (fun i hi => by rw [FR_get (ld_lt hi)]; exact rst_facts.1 j hj i hi)
    (unpack_rng (allN_spec run_perms (Nat.add 8 j) (by simp only [Nat.add_eq]; omega)))

theorem binds : Binds 280 9 S2308LC.S 14 4 S2308LC.BP localStrongArrs localBaseNat.toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [localStrongArrs], fun j hj => ?_, by
    simp [localBaseNat], fun t ht => ?_⟩
  · rw [getElem!_pos _ j (by simp [localStrongArrs]; exact hj)]
    simp only [localStrongArrs, Array.getElem_ofFn]
    rw [loc_get (k := 8 + j) (by omega), rst_facts.2.2.2.2.2.1 j hj]
    rfl
  · rw [← rst_facts.2.2.2.2.2.2 t ht]
    interval_cases t <;> rfl

theorem gen_eq : localStrongArrs.extract 0 8 = localGenArrs := by
  apply Array.ext
  · simp [localStrongArrs, localGenArrs]
  · intro i h1 h2
    have hi : i < 8 := by simpa [localGenArrs] using h2
    simp only [Array.getElem_extract, localStrongArrs, localGenArrs, Array.getElem_ofFn, Nat.zero_add]
    have e := rst_facts.2.2.2.2.1 i hi
    simp only [Nat.add_eq] at e
    rw [loc_get (k := 8 + i) (by omega), loc_get (k := i) (by omega), ← e]

theorem orb_eq : rawOrbitSizes 280 localStrongArrs localBaseNat.toArray = [280, 36, 216, 3] := by
  rw [rawOrbitSizesK_sound binds lperm S2308LC.hl]
  decide

theorem chain_ok :
    rawChainOK 280 localGenArrs localStrongArrs localBaseNat.toArray localDerivs 4 = true := by
  have h := rawChainK_sound (NS := 1) (CH := 280) (chunks := 4) binds S2308LC.head S2308LC.hl
    (by norm_num) S2308LC.hs
  have hw : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 8 14 S2308M.dM = localDerivs := by decide
  rwa [gen_eq, hw] at h

theorem localChecks_ok : localChecks fullExtArrs = true := by
  unfold localChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨full_size, dom_len⟩, ?_⟩, ?_⟩, chain_ok⟩, by rw [orb_eq]; rfl⟩, by rw [orb_eq]; rfl⟩
  · rw [alt_iff]
    intro k hk
    rw [beq_iff_eq]
    have e : certStrongArrs[localStrongIdx.getD k 0]! = FR k := by
      rw [FR_base hk]
      interval_cases k <;> simp [localStrongIdx, certStrongArrs]
    rw [e, restrict_F (j := k) (by omega),
      getElem!_pos localGenArrs k (by simp [localGenArrs]; exact hk)]
    simp only [localGenArrs, Array.getElem_ofFn]
    rw [loc_get (k := k) (by omega), ← rst_facts.2.2.2.2.1 k hk]
  · rw [alt_iff]
    intro j hj
    rw [Bool.and_eq_true, beq_iff_eq, full_get hj, (F_inv hj).1, restrict_F hj]
    refine ⟨(F_inv hj).2, ?_⟩
    rw [getElem!_pos localStrongArrs j (by simp [localStrongArrs]; exact hj)]
    simp only [localStrongArrs, Array.getElem_ofFn]
    rw [loc_get (k := 8 + j) (by omega)]
    rfl

theorem pen_facts : szOK 280 9 = true ∧ (∀ a < 5, canonK 280 9 (mask 9) (280 * 9) (S2308CE.G a) = true) ∧
    S2308CE.k = 5 ∧ S2308CE.cnt = 729 ∧ canonK 280 9 (mask 9) (280 * 9) (SuzCenC 3) = true ∧
    SuzCenC 3 ≠ pidn 280 9 ∧ penumHdK (pidn 280 9) S2308CE.cnt 729 S2308CE.T S2308CE.PL = true := by
  have h := pen
  simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, fun a ha => allN_spec h2 a ha, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, h5,
    fun e => ?_, h7⟩
  rw [e, Nat.beq_refl] at h6
  exact absurd h6 (by decide)

theorem pts_all {i : Nat} (hi : i < S2308CE.cnt) : penumPtK 280 9 (mask 9) (280 * 9) false
    S2308CE.G S2308CE.GI 5 S2308CE.cnt S2308CE.T S2308CE.PL S2308CE.POS S2308CE.SRT S2308CE.SRI i =
      true := by
  rcases Nat.lt_or_ge i 365 with h | h
  · exact penumSl_spec pts0 i (by omega) (by omega) hi
  · exact penumSl_spec pts1 i h (by have := pen_facts.2.2.2.1; omega) hi

theorem C_get {a : Nat} (ha : a < 5) :
    (tCompOf (tFullOf fullExtArrs))[a]! = unpack 280 9 (S2308CE.G a) := by
  rw [tCompOf, map_get (by rw [T_size]; exact ha), T_get ha]
  exact restrict_eq (fun i hi => by rw [TR, rowArr_get (ld_lt hi)]; exact rst_facts.2.1 a ha i hi)
    (canon_rng (pen_facts.2.1 a ha))

theorem gensC : GensOK 280 9 5 S2308CE.G (tCompOf (tFullOf fullExtArrs)) :=
  ⟨by simp [tCompOf, T_size], fun a ha => ⟨C_get ha, pen_facts.2.1 a ha⟩⟩

theorem enumC : compactEnum (tFullOf fullExtArrs) = penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL ∧
    enumOK 280 (tCompOf (tFullOf fullExtArrs))
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL) = true :=
  penumK_left_sound (cap := 729) pen_facts.1 gensC pen_facts.2.2.2.2.2.2 (fun _ hi => pts_all hi)

theorem rec_get {i : Nat} (hi : i < S2308CE.cnt) :
    (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[i]! = unpack 280 9 (S2308CE.T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem unpack_ne {p q : Nat} (hp : canonK 280 9 (mask 9) (280 * 9) p = true)
    (hq : canonK 280 9 (mask 9) (280 * 9) q = true) (h : p ≠ q) : unpack 280 9 p ≠ unpack 280 9 q :=
  fun e => h (CFSG.KS.MulH.unpack_injH hp hq e)

theorem beq_unpack {p q : Nat} (hp : canonK 280 9 (mask 9) (280 * 9) p = true)
    (hq : canonK 280 9 (mask 9) (280 * 9) q = true) :
    (unpack 280 9 p == unpack 280 9 q) = Nat.beq p q := by
  cases e : Nat.beq p q
  · rw [beq_eq_false_iff_ne]
    exact unpack_ne hp hq (fun h => by rw [h, Nat.beq_refl] at e; exact absurd e (by decide))
  · rw [Nat.eq_of_beq_eq_true e]
    exact beq_self_eq_true _

theorem allN_false {n : Nat} {f : Nat → Bool} (h : allN n f = false) : ∃ i < n, f i = false := by
  by_contra hc
  push_neg at hc
  have := CFSG.KS.PackFld.allN_of_forall (n := n) (f := f) fun i hi => by
    cases e : f i
    · exact absurd e (hc i hi)
    · rfl
  rw [this] at h
  exact absurd h (by decide)

theorem id_canon : canonK 280 9 (mask 9) (280 * 9) (pidn 280 9) = true := by
  have h := nw
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact h.1

theorem idTab280 : idTab 280 = unpack 280 9 (pidn 280 9) := CFSG.KC.BfsPin.idA_eq pen_facts.1

theorem scan_ok : allLt (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs.size (fun k =>
    !(allLt 5 fun a => comp 280 (tCompOf (tFullOf fullExtArrs))[a]!
        (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! ==
      comp 280 (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]!
        (tCompOf (tFullOf fullExtArrs))[a]!) ||
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! == idTab 280 ||
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! == centerCompact 3 ||
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! ==
        comp 280 (centerCompact 3) (centerCompact 3)) = true := by
  rw [alt_iff]
  intro k hk
  have hk' : k < S2308CE.cnt := by simpa [penumRec] using hk
  have hc := penumPt_canon (pts_all hk')
  have hcc := pen_facts.2.2.2.2.1
  have he := allN_spec esc k (by rw [← pen_facts.2.2.2.1]; exact hk')
  unfold escP at he
  rw [strictB_app'] at he
  have hcomm : (allLt 5 fun a => comp 280 (tCompOf (tFullOf fullExtArrs))[a]!
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! ==
    comp 280 (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]!
      (tCompOf (tFullOf fullExtArrs))[a]!) = allN 5 (fun a => Nat.beq
        (pcomp 280 9 (mask 9) (S2308CE.G a) (S2308CE.T k))
        (pcomp 280 9 (mask 9) (S2308CE.T k) (S2308CE.G a))) := by
    have hpt : ∀ a < 5, (comp 280 (tCompOf (tFullOf fullExtArrs))[a]!
        (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! ==
      comp 280 (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]!
        (tCompOf (tFullOf fullExtArrs))[a]!) = Nat.beq
          (pcomp 280 9 (mask 9) (S2308CE.G a) (S2308CE.T k))
          (pcomp 280 9 (mask 9) (S2308CE.T k) (S2308CE.G a)) := by
      intro a ha
      have hg := pen_facts.2.1 a ha
      rw [C_get ha, rec_get hk', comp_eqA, comp_eqA,
        CFSG.KC.BfsPin.compA_unpack hg hc, CFSG.KC.BfsPin.compA_unpack hc hg]
      exact beq_unpack (CFSG.KC.BfsPin.canonK_pcomp hg hc) (CFSG.KC.BfsPin.canonK_pcomp hc hg)
    cases e : allN 5 (fun a => Nat.beq (pcomp 280 9 (mask 9) (S2308CE.G a) (S2308CE.T k))
        (pcomp 280 9 (mask 9) (S2308CE.T k) (S2308CE.G a)))
    · obtain ⟨a, ha, hf⟩ := allN_false e
      cases e2 : allLt 5 _
      · rfl
      · have := alt_iff.1 e2 a ha
        rw [hpt a ha, hf] at this
        exact absurd this (by decide)
    · exact alt_iff.2 fun a ha => by rw [hpt a ha]; exact allN_spec e a ha
  rw [hcomm]
  revert he
  cases allN 5 (fun a => Nat.beq (pcomp 280 9 (mask 9) (S2308CE.G a) (S2308CE.T k))
      (pcomp 280 9 (mask 9) (S2308CE.T k) (S2308CE.G a)))
  · intro _
    rfl
  · intro he
    rw [rec_get hk', idTab280, centerCompact_eq (r := 3) (by norm_num), comp_eqA,
      CFSG.KC.BfsPin.compA_unpack hcc hcc, beq_unpack hc id_canon, beq_unpack hc hcc,
      beq_unpack hc (CFSG.KC.BfsPin.canonK_pcomp hcc hcc)]
    simp only [Bool.not_true, Bool.false_or]
    revert he
    cases Nat.beq (S2308CE.T k) (pidn 280 9) <;> cases Nat.beq (S2308CE.T k) (SuzCenC 3) <;> simp

theorem cen_all : ∀ x < 22880, cenP x = true := qtr_all cq0 cq1 cq2 cq3

theorem cf_lt {r x : Nat} (hr : r < 9) (hx : x < 22880) : cf r x < 22880 := cen_lt hr hx

theorem powArr_get' {t : Array Nat} {f : Nat → Nat} (ht : ∀ y < 22880, t[y]! = f y)
    (hf : ∀ y < 22880, f y < 22880) : ∀ k, ∀ x < 22880, (powArr 22880 t k)[x]! = itr f k x
  | 0, x, hx => by rw [powArr, idA_get hx]; rfl
  | k + 1, x, hx => by
    rw [powArr, compA_get hx, powArr_get' ht hf k x hx, itr_succ,
      ht _ (itr_congr (fun y _ => rfl) hf k x hx).2]

theorem cenP_facts {x : Nat} (hx : x < 22880) :
    (∀ r < 9, cf r x = o2 (itr (cf 3) (Nat.div r 3)) (itr zx (Nat.mod r 3)) x) ∧
    o2 (cf 1) (cf 1) x = cf 2 x ∧ o2 (cf 3) (cf 3) x = cf 6 x ∧ o2 (cf 4) (cf 4) x = cf 8 x ∧
    o2 (cf 5) (cf 5) x = cf 7 x ∧ cf 3 x = tx 1 x ∧ o2 (cf 3) zx x = o2 zx (cf 3) x ∧
    (∀ a < 5, o2 (cf 3) (tx a) x = o2 (tx a) (cf 3) x ∧ o2 zx (tx a) x = o2 (tx a) zx x) ∧
    itr (cf 3) 3 x = x := by
  have h := cen_all x hx
  unfold cenP at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨fun r hr => Nat.eq_of_beq_eq_true (allN_spec h1 r hr), Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5,
    Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7, fun a ha => ?_, Nat.eq_of_beq_eq_true h9⟩
  have e := allN_spec h8 a ha
  simp only [bAnd_eq, Bool.and_eq_true] at e
  exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2⟩

theorem T1_get {a x : Nat} (ha : a < 5) (hx : x < 22880) :
    ((tFullOf fullExtArrs)[a]!)[x]! = tx a x := by
  rw [T_get ha, TR, rowArr_get hx]
  rfl

theorem comm_eqA {t u : Array Nat} {f g : Nat → Nat} (ht : ∀ y < 22880, t[y]! = f y)
    (hu : ∀ y < 22880, u[y]! = g y) (hf : ∀ y < 22880, f y < 22880) (hg : ∀ y < 22880, g y < 22880)
    (h : ∀ x < 22880, o2 f g x = o2 g f x) :
    eqA 22880 (compA 22880 t u) (compA 22880 u t) = true :=
  eqA_true fun x hx => by
    have := h x hx
    rw [o2_eq, o2_eq] at this
    rw [compA_get hx, compA_get hx, hu x hx, ht x hx, ht _ (hg x hx), hu _ (hf x hx), this]

theorem sq_eqA {r r' : Nat} (hr : r < 9) (hr' : r' < 9) (h : ∀ x < 22880, o2 (cf r) (cf r) x = cf r' x) :
    eqA 22880 (compA 22880 (centerFull r) (centerFull r)) (centerFull r') = true :=
  eqA_true fun x hx => by
    rw [compA_get hx, cen_get hr hx, cen_get hr (cf_lt hr hx), cen_get hr' hx, ← h x hx, o2_eq]

theorem sylow_ok : sylowCenterChecks (tFullOf fullExtArrs) (compactEnum (tFullOf fullExtArrs)) =
    true := by
  have hz : ∀ y < 22880, zArr[y]! = zx y := fun y hy => (z_get hy).1
  have hzl : ∀ y < 22880, zx y < 22880 := fun y hy => (z_get hy).2
  have hc : ∀ y < 22880, (centerFull 3)[y]! = cf 3 y := fun y hy => cen_get (by norm_num) hy
  have hcl : ∀ y < 22880, cf 3 y < 22880 := fun y hy => cf_lt (by norm_num) hy
  unfold sylowCenterChecks
  rw [enumC.1]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨enumC.2, by simp [penumRec, pen_facts.2.2.2.1]⟩, scan_ok⟩, ?_⟩, ?_⟩,
    sq_eqA (by norm_num) (by norm_num) fun x hx => (cenP_facts hx).2.1⟩,
    sq_eqA (by norm_num) (by norm_num) fun x hx => (cenP_facts hx).2.2.1⟩,
    sq_eqA (by norm_num) (by norm_num) fun x hx => (cenP_facts hx).2.2.2.1⟩,
    sq_eqA (by norm_num) (by norm_num) fun x hx => (cenP_facts hx).2.2.2.2.1⟩, ?_⟩, ?_⟩, ?_⟩,
    comm_eqA hc hz hcl hzl fun x hx => (cenP_facts hx).2.2.2.2.2.2.1⟩, ?_⟩, ?_⟩
  · rw [alt_iff]
    intro r hr
    rw [Bool.and_eq_true]
    refine ⟨cen_perm hr, eqA_true fun x hx => ?_⟩
    have hy := (itr_congr (fun y _ => rfl) hzl (r % 3) x hx).2
    rw [cen_get hr hx, (cenP_facts hx).1 r hr, compA_get hx,
      powArr_get' hz hzl (r % 3) x hx, powArr_get' hc hcl (r / 3) _ hy, o2_eq]
    rfl
  · rw [alt_iff]
    intro r hr
    rw [alt_iff]
    intro r' hr'
    have h := allN_spec (allN_spec cdist r hr) r' hr'
    by_cases hlt : r < r'
    · have hb : Nat.blt r r' = true := by
        rw [Nat.blt_eq]
        exact hlt
      rw [hb] at h
      simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
      have hp := Eq.mp Nat.blt_eq h.1
      rw [decide_eq_true hlt, Bool.not_true, Bool.false_or, Bool.not_eq_true']
      refine eqA_false hp ?_
      rw [cen_get hr hp, cen_get hr' hp]
      intro e
      rw [e, Nat.beq_refl] at h
      exact absurd h.2 (by decide)
    · rw [decide_eq_false hlt]
      rfl
  · exact eqA_true fun x hx => by rw [hc x hx, T1_get (a := 1) (by norm_num) hx]; exact (cenP_facts hx).2.2.2.2.2.1
  · rw [centerCompact_eq (r := 3) (by norm_num)]
    exact restrict_eq (fun i hi => by rw [hc _ (ld_lt hi)]; exact rst_facts.2.2.1 i hi)
      (canon_rng pen_facts.2.2.2.2.1)
  · rw [Bool.not_eq_true', centerCompact_eq (r := 3) (by norm_num), idTab280,
      beq_unpack pen_facts.2.2.2.2.1 id_canon]
    cases e : Nat.beq (SuzCenC 3) (pidn 280 9)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) pen_facts.2.2.2.2.2.1
  · rw [alt_iff]
    intro a ha
    rw [Bool.and_eq_true]
    have ht : ∀ y < 22880, ((tFullOf fullExtArrs)[a]!)[y]! = tx a y := fun y hy => T1_get ha hy
    have htl : ∀ y < 22880, tx a y < 22880 := fun y hy => tx_lt ha hy
    exact ⟨comm_eqA hc ht hcl htl fun x hx => ((cenP_facts hx).2.2.2.2.2.2.2.1 a ha).1,
      comm_eqA hz ht hzl htl fun x hx => ((cenP_facts hx).2.2.2.2.2.2.2.1 a ha).2⟩
  · exact eqA_true fun x hx => by
      rw [powArr_get' hc hcl 3 x hx, (cenP_facts hx).2.2.2.2.2.2.2.2, idA_get hx]

theorem g_get {x : Nat} (hx : x < 22880) : fusionTransArr[x]! = gx x := by
  have hS : ∀ j < 2, (#[certArr 0, certArr 1] : Array (Array Nat))[j]! = rowArr 22880 15 SuzCertT.F (ofs j) :=
    fun j hj => by interval_cases j <;> simp [certArr_eq] <;> rfl
  have hSi : ∀ j < 2, (#[invCand 22880 (certArr 0), invCand 22880 (certArr 1)] : Array (Array Nat))[j]! =
      rowArr 22880 15 SuzCertI (ofs j) := fun j hj => by
    interval_cases j <;> simp [cert_inv] <;> rfl
  have h := rwordPt_eq (kS := 2) (O := ofs) hS hSi (fun j hj => cert_rngF (by omega))
    (fun j hj => cert_rngG (by omega)) fusW (by decide) x hx
  have hg : ∀ y < 22880, gP y = true := qtr_all gq0 gq1 gq2 gq3
  have e := hg x hx
  unfold gP at e
  simp only [bAnd_eq, Bool.and_eq_true] at e
  rw [Nat.eq_of_beq_eq_true e.1]
  exact h.1

theorem g_eq : fusionTransArr = rowArr 22880 15 S2308GX 0 :=
  arr_eq (size_wordA _ _ _ _) (size_rowArr _ _ _ _) fun x hx => by rw [g_get hx, rowArr_get hx]; rfl

theorem fixed_count {r : Nat} (hr : r < 9) (h : cntK 22880 (fun i => Nat.beq (cf r i) i) = 38) :
    fixedCountN 22880 (centerFull r) = 38 := by
  have hfc : (List.range 22880).filter (fun x => (centerFull r)[x]! == x) =
      (List.range 22880).filter (fun i => Nat.beq (cf r i) i) := by
    apply List.filter_congr
    intro x hx
    rw [List.mem_range] at hx
    rw [cen_get hr hx, beq_nat]
  unfold CFSG.Sporadic.SuzOddCore.fixedCountN CFSG.Sporadic.SuzOddCore.fixedList
  rw [hfc, ← cntK_eq, h]

theorem pos_word {S Sinv : Array (Array Nat)} {n : Nat} :
    ∀ w : List Int, (∀ l ∈ w, 0 < l) →
      wordA n S Sinv w = (w.map fun l => l.toNat - 1).foldr (fun j acc => comp n S[j]! acc) (idTab n)
  | [], _ => rfl
  | l :: w, h => by
    have hl := h l List.mem_cons_self
    rw [wordA, pos_word w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')), List.map_cons,
      List.foldr_cons, comp_eqA]
    congr 1
    unfold letterA
    simp [hl]

theorem nw_facts : (∀ k < 8, canonK 280 9 (mask 9) (280 * 9) (SuzLocR k) = true ∧
      canonK 280 9 (mask 9) (280 * 9) (SuzLocRI k) = true) ∧
    (∀ k < 39, invEqK 280 9 (mask 9) (280 * 9) (nwK k) (nwiK k) = true) ∧
    (∀ k < 39, ∀ k' < 39, k < k' → ncK k ≠ ncK k' ∧ ncK k ≠ pcomp 280 9 (mask 9) (ncK k') (ncK k')) := by
  have h := nw
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk k' hk' hlt => ?_⟩
  · have e := allN_spec h2 k hk
    simp only [bAnd_eq, Bool.and_eq_true] at e
    exact e
  · have e := allN_spec h3 k hk
    simp only [bAnd_eq, Bool.and_eq_true] at e
    exact e.2
  · have e := allN_spec h4 k hk
    rw [strictB_app'] at e
    have e2 := allN_spec e k' hk'
    have hb : Nat.blt k k' = true := by
      rw [Nat.blt_eq]
      exact hlt
    rw [hb] at e2
    change strictB (ncK k') _ = true at e2
    rw [strictB_app'] at e2
    simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at e2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, Nat.beq_refl] at e2
      exact absurd e2.1 (by decide)
    · rw [h, Nat.beq_refl] at e2
      exact absurd e2.2 (by decide)

theorem nwN_lt : ∀ k < 39, ∀ j ∈ nwN k, j < 8 := by decide

theorem nw_pos : ∀ k < 39, ∀ l ∈ normWords.getD k [], 0 < l := by decide

theorem lg_get {j : Nat} (hj : j < 8) : localGenArrs[j]! = unpack 280 9 (SuzLocR j) := by
  rw [getElem!_pos localGenArrs j (by simp [localGenArrs]; exact hj)]
  simp only [localGenArrs, Array.getElem_ofFn]
  exact loc_get (by omega)

theorem nwK_canon {k : Nat} (hk : k < 39) : normWordArr k = unpack 280 9 (nwK k) ∧
    canonK 280 9 (mask 9) (280 * 9) (nwK k) = true := by
  unfold normWordArr
  rw [pos_word _ (nw_pos k hk)]
  exact wordTabK_eq idTab280 id_canon (nwN k) fun j hj =>
    ⟨lg_get (nwN_lt k hk j hj), (nw_facts.1 j (nwN_lt k hk j hj)).1⟩

theorem nwiK_canon {k : Nat} (hk : k < 39) : canonK 280 9 (mask 9) (280 * 9) (nwiK k) = true := by
  have := wordTabK_eq (gs := Array.ofFn (n := 8) fun j => unpack 280 9 (SuzLocRI j.val))
    idTab280 id_canon (nwN k).reverse fun j hj => by
      have hj8 := nwN_lt k hk j (List.mem_reverse.1 hj)
      refine ⟨?_, (nw_facts.1 j hj8).2⟩
      rw [getElem!_pos _ j (by simp; exact hj8), Array.getElem_ofFn]
  exact this.2

theorem nc_eq {k : Nat} (hk : k < 39) : normConj k = unpack 280 9 (ncK k) ∧
    canonK 280 9 (mask 9) (280 * 9) (ncK k) = true := by
  have hw := nwK_canon hk
  have hi := invEqK_sound (nw_facts.2.1 k hk)
  have hwi := nwiK_canon hk
  have hcc := pen_facts.2.2.2.2.1
  unfold normConj
  rw [hw.1, hi.1, centerCompact_eq (r := 3) (by norm_num), CFSG.KC.BfsPin.compA_unpack hcc hwi,
    CFSG.KC.BfsPin.compA_unpack hw.2 (CFSG.KC.BfsPin.canonK_pcomp hcc hwi)]
  exact ⟨rfl, CFSG.KC.BfsPin.canonK_pcomp hw.2 (CFSG.KC.BfsPin.canonK_pcomp hcc hwi)⟩

theorem eqA_unpack_false {p q : Nat} (hp : canonK 280 9 (mask 9) (280 * 9) p = true)
    (hq : canonK 280 9 (mask 9) (280 * 9) q = true) (h : p ≠ q) :
    eqA 280 (unpack 280 9 p) (unpack 280 9 q) = false := by
  cases e : eqA 280 (unpack 280 9 p) (unpack 280 9 q)
  · rfl
  · refine absurd (arr_eq (n := 280) (by simp [unpack]) (by simp [unpack]) fun x hx => ?_) (unpack_ne hp hq h)
    exact beq_iff_eq.1 (alt_iff.1 e x hx)

theorem fusion_ok : fusionNormChecks = true := by
  have hz : ∀ y < 22880, zArr[y]! = zx y := fun y hy => (z_get hy).1
  have hg := rpermK_sound ((by simpa only [bAnd_eq, Bool.and_eq_true] using gperm :
    rpermK 22880 15 (mask 15) S2308GX 0 S2308GXI 0 = true ∧ Nat.beq (gx 0) 95 = true).1)
  have hg95 := ((by simpa only [bAnd_eq, Bool.and_eq_true] using gperm :
    rpermK 22880 15 (mask 15) S2308GX 0 S2308GXI 0 = true ∧ Nat.beq (gx 0) 95 = true).2)
  have hgP : ∀ y < 22880, gP y = true := qtr_all gq0 gq1 gq2 gq3
  have hc := zpts
  simp only [bAnd_eq, Bool.and_eq_true] at hc
  unfold fusionNormChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, fixed_count (by norm_num) (Nat.eq_of_beq_eq_true hc.2.2.2.2.1)⟩,
    fixed_count (by norm_num) (Nat.eq_of_beq_eq_true hc.2.2.2.2.2)⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [g_eq, hg.1]
    exact hg.2
  · rw [g_eq, hg.1]
    refine eqA_true fun x hx => ?_
    have hy : rg 15 (mask 15) S2308GXI 0 x < 22880 := rpermK_range gpermR x hx
    have e := hgP x hx
    unfold gP at e
    simp only [bAnd_eq, Bool.and_eq_true] at e
    rw [compA_get hx, compA_get hx, rowArr_get hx, hz _ hy, rowArr_get (z_get hy).2,
      cen_get (by norm_num) hx, ← Nat.eq_of_beq_eq_true e.2, o2_eq, o2_eq]
    rfl
  · rw [g_get (x := 0) (by norm_num)]
    exact Nat.eq_of_beq_eq_true hg95
  · rw [alt_iff]
    intro k hk
    rw [(nwK_canon hk).1, (invEqK_sound (nw_facts.2.1 k hk)).1]
    exact (invEqK_sound (nw_facts.2.1 k hk)).2
  · rw [alt_iff]
    intro k hk
    rw [lg_get hk, (invEqK_sound (allN_spec run_perms k (by omega))).1]
    exact (invEqK_sound (allN_spec run_perms k (by omega))).2
  · rw [alt_iff]
    intro k hk
    rw [alt_iff]
    intro k' hk'
    by_cases hlt : k < k'
    · rw [decide_eq_true hlt, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
        Bool.not_eq_true', (nc_eq hk).1, (nc_eq hk').1, CFSG.KC.BfsPin.compA_unpack (nc_eq hk').2
          (nc_eq hk').2]
      obtain ⟨n1, n2⟩ := nw_facts.2.2 k hk k' hk' hlt
      exact ⟨eqA_unpack_false (nc_eq hk).2 (nc_eq hk').2 n1,
        eqA_unpack_false (nc_eq hk).2 (CFSG.KC.BfsPin.canonK_pcomp (nc_eq hk').2 (nc_eq hk').2) n2⟩
    · rw [decide_eq_false hlt]
      rfl

theorem facts2308 :
    threeChecks fullExtArrs (tFullOf fullExtArrs) (compactEnum (tFullOf fullExtArrs)) = true := by
  unfold threeChecks
  rw [zChecks_ok, localChecks_ok, sylow_ok, fusion_ok]
  rfl

end CertificateChecks.KernelSpor.OddCore.S2308

end
