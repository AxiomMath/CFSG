
module

public import Certificates.Kernel.Sporadic.Fi22.T2068
public import CFSG.Certificates.Kernel.Spor.LevelTrSound
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22LabA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Text
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22LabX

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem unpack_get' {n w P x : Nat} (hx : x < n) : (unpack n w P)[x]! = pg w (mask w) P x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem cn_lt {q : Nat} (h : Fi22X.cn q = true) : ∀ x < 3510, pg 12 (mask 12) q x < 3510 := by
  have h' : bAnd(szOK 3510 12, bAnd(Nat.beq (Nat.shiftRight q (3510 * 12)) (nat_lit 0),
      allN 3510 (fun i => Nat.blt (pg 12 (mask 12) q i) 3510))) = true := h
  obtain ⟨-, h2⟩ := (bAnd_iff (szOK 3510 12) (bAnd(Nat.beq (Nat.shiftRight q (3510 * 12))
    (nat_lit 0), allN 3510 (fun i => Nat.blt (pg 12 (mask 12) q i) 3510)))).1 h'
  have h3 := ((bAnd_iff (Nat.beq (Nat.shiftRight q (3510 * 12)) (nat_lit 0))
    (allN 3510 (fun i => Nat.blt (pg 12 (mask 12) q i) 3510))).1 h2).2
  intro x hx
  exact Nat.blt_eq ▸ allN_spec h3 x hx

theorem eqA_of_get {t u : Array Nat} (h : ∀ z < 3510, t[z]! = u[z]!) : eqA 3510 t u = true := by
  rw [eqA, allLt_iff]
  intro z hz
  rw [beq_iff_eq, h z hz]

theorem not_allN {n : Nat} {f : Nat → Bool} (h : Bool.not (allN n f) = true) :
    ∃ i < n, f i ≠ true := by
  by_contra hc
  push Not at hc
  rw [allN_of_forall hc] at h
  exact absurd h (by decide)

theorem parLt_of_forall {n chunks : ℕ} {p : ℕ → Bool} (h : ∀ i < n, p i = true) :
    parLt n chunks p = true := by
  unfold parLt
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  change allLt (n / chunks + 1) (fun k => !(decide (c * (n / chunks + 1) + k < n)) ||
    p (c * (n / chunks + 1) + k)) = true
  refine allLt_iff.2 fun k _ => ?_
  by_cases hk : c * (n / chunks + 1) + k < n
  · simp [h _ hk]
  · simp [hk]

theorem countP_range_eq {N M : ℕ} {f g : ℕ → Bool} (φ ψ : ℕ → ℕ)
    (h1 : ∀ I < N, f I = true → φ I < M ∧ g (φ I) = true ∧ ψ (φ I) = I)
    (h2 : ∀ k < M, g k = true → ψ k < N ∧ f (ψ k) = true ∧ φ (ψ k) = k) :
    (List.range N).countP f = (List.range M).countP g := by
  rw [← card_fin_subtype_eq_countP, ← card_fin_subtype_eq_countP]
  refine Nat.card_congr
    { toFun := fun I => ⟨⟨φ I.1, (h1 I.1 I.1.2 I.2).1⟩, (h1 I.1 I.1.2 I.2).2.1⟩
      invFun := fun k => ⟨⟨ψ k.1, (h2 k.1 k.1.2 k.2).1⟩, (h2 k.1 k.1.2 k.2).2.1⟩
      left_inv := fun I => Subtype.ext (Fin.ext (h1 I.1 I.1.2 I.2).2.2)
      right_inv := fun k => Subtype.ext (Fin.ext (h2 k.1 k.1.2 k.2).2.2) }

theorem countP_range_rec {f g : ℕ → Bool} : ∀ m, (∀ i < m, f i = g i) →
    (List.range m).countP f =
      Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (nIf(g i, 1, 0))) m
  | 0, _ => rfl
  | m + 1, h => by
    rw [List.range_succ, List.countP_append, countP_range_rec m (fun i hi => h i (by omega))]
    have hm := h m (by omega)
    change _ = Nat.add _ (nIf(g m, 1, 0))
    simp only [List.countP_cons, List.countP_nil, hm]
    cases g m <;> simp

theorem fixCount_eq {p : Nat} : fixCount 3510 (unpack 3510 12 p) = fixK p := by
  unfold fixCount fixK
  refine countP_range_rec (f := fun i => (unpack 3510 12 p)[i]! == i)
    (g := fun i => Nat.beq (pg 12 (mask 12) p i) i) 3510 fun i hi => ?_
  rw [unpack_get' hi]
  cases h : Nat.beq (pg 12 (mask 12) p i) i
  · simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun he => by rw [he, Nat.beq_refl] at h; exact Bool.noConfusion h
  · simp only [beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h

theorem offs_parts : roff 3510 (3510 * 12) (Fi22TC.LR 0) = 0 ∧
    roff 3510 (3510 * 12) (Fi22TC.LR 1) = 1024 ∧ roff 3510 (3510 * 12) (Fi22TC.LR 2) = 1056 ∧
    rcnt (Fi22TC.LR 0) = 1024 ∧ rcnt (Fi22TC.LR 1) = 32 ∧ rcnt (Fi22TC.LR 2) = 4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := by simpa only [bAnd_iff] using offs
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

theorem tr_cn {k : Nat} (hk : k < 1060) : Fi22X.cn (Fi22TC.TR k) = true := by
  have hq : k / 20 < 53 := by omega
  have h := allN_spec (trAll (k / 20) hq) (k % 20) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (k / 20) 20) (k % 20) = k := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [strictB_eq', e] at h
  exact bIf_of_true (Nat.blt_eq ▸ hk) h

theorem row_at {I : Nat} (hI : I < 262144) : rowI I = true := by
  have hq : I / 512 < 512 := by omega
  have h := allN_spec (rowAll (I / 512) hq) (I % 512) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (I / 512) 512) (I % 512) = I := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [e] at h

theorem inv_at {k : Nat} (hk : k < 6143) : invRow k = true := by
  have hq : k / 64 < 96 := by omega
  have h := allN_spec (invAll (k / 64) hq) (k % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (k / 64) 64) (k % 64) = k := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [strictB_eq', e] at h
  exact bIf_of_true (Nat.blt_eq ▸ hk) h

theorem root_at {j : Nat} (hj : j < 79) : rootRow j = true := by
  have hq : j / 8 < 10 := by omega
  have h := allN_spec (rootAll (j / 8) hq) (j % 8) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (j / 8) 8) (j % 8) = j := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [strictB_eq', e] at h
  exact bIf_of_true (Nat.blt_eq ▸ hj) h

theorem conj_at {j : Nat} (hj : j < 79) : conjRow j = true := by
  have hq : j / 8 < 10 := by omega
  have h := allN_spec (conjAll (j / 8) hq) (j % 8) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (j / 8) 8) (j % 8) = j := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [strictB_eq', e] at h
  exact bIf_of_true (Nat.blt_eq ▸ hj) h

theorem inv_parts {k : Nat} (hk : k < 6143) :
    PP (SV k) = k ∧ SV k < 262144 ∧ (k + 1 < 6143 → SV k < SV (k + 1)) := by
  have h := inv_at hk
  unfold invRow at h
  obtain ⟨h1, h2, h3⟩ := by simpa only [bAnd_iff] using h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.blt_eq ▸ h2, fun hk1 => ?_⟩
  rw [show Nat.blt (Nat.add k 1) 6143 = true from Eq.mpr Nat.blt_eq hk1] at h3
  exact Nat.blt_eq ▸ h3

theorem root_parts {j : Nat} (hj : j < 79) :
    fi22ExtRootsRec[j]! = RT j ∧ RT j < 262144 ∧ labOf (RT j) = j ∧
      ∀ p < 3510, XI (RT j) p = pg 12 (mask 12) (Lx (27 + j)) p := by
  have h := root_at hj
  unfold rootRow at h
  obtain ⟨h1, h2, h3, h4⟩ := by simpa only [bAnd_iff] using h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.blt_eq ▸ h2, Nat.eq_of_beq_eq_true h3,
    fun p hp => Nat.eq_of_beq_eq_true (allN_spec h4 p hp)⟩

theorem row_inv {I : Nat} (hI : I < 262144) (hinv : isInvK I = true) :
    PP I < 6143 ∧ SV (PP I) = I ∧ LB (PP I) < 79 ∧
    (DE (PP I) = 0 → I = RT (LB (PP I))) ∧
    (DE (PP I) ≠ 0 → PR (PP I) < 262144 ∧ depOf (PR (PP I)) < DE (PP I) ∧
      labOf (PR (PP I)) = LB (PP I) ∧ GN (PP I) < 10 ∧ conjB (GN (PP I)) I (PR (PP I)) = true) ∧
    ∀ s < 10, NB (PP I * 10 + s) < 262144 ∧ labOf (NB (PP I * 10 + s)) = LB (PP I) ∧
      conjB s (NB (PP I * 10 + s)) I = true := by
  have h := row_at hI
  unfold rowI at h
  rw [strictB_eq', hinv] at h
  change bAnd(Nat.blt (PP I) 6143, bAnd(Nat.beq (SV (PP I)) I, strictB (LB (PP I)) _)) = true at h
  obtain ⟨h1, h2, h3⟩ := by simpa only [bAnd_iff] using h
  rw [strictB_eq'] at h3
  obtain ⟨h4, h5, h6⟩ := by simpa only [bAnd_iff] using h3
  refine ⟨Nat.blt_eq ▸ h1, Nat.eq_of_beq_eq_true h2, Nat.blt_eq ▸ h4, fun hd => ?_, fun hd => ?_,
    fun s hs => ?_⟩
  · rw [show Nat.beq (DE (PP I)) 0 = true from Eq.mpr Nat.beq_eq hd] at h5
    exact Nat.eq_of_beq_eq_true h5
  · have hb : Nat.beq (DE (PP I)) 0 = false := by
      cases e : Nat.beq (DE (PP I)) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hd
    rw [hb, strictB_eq', strictB_eq'] at h5
    obtain ⟨a, b, c, d, e⟩ := by simpa only [bAnd_iff] using h5
    exact ⟨Nat.blt_eq ▸ a, Nat.blt_eq ▸ b, Nat.eq_of_beq_eq_true c, Nat.blt_eq ▸ d, e⟩
  · have h7 := allN_spec h6 s hs
    rw [strictB_eq'] at h7
    obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using h7
    rw [Nat.add_eq, Nat.mul_eq] at a b c
    exact ⟨Nat.blt_eq ▸ a, Nat.eq_of_beq_eq_true b, c⟩

theorem row_noinv {I : Nat} (hI : I < 262144) (hinv : isInvK I = false) : PP I = 6143 := by
  have h := row_at hI
  unfold rowI at h
  rw [strictB_eq', hinv] at h
  exact Nat.eq_of_beq_eq_true h

theorem pp_lt_inv {I : Nat} (hI : I < 262144) (h : PP I < 6143) : isInvK I = true := by
  cases e : isInvK I
  · rw [row_noinv hI e] at h
    exact absurd h (lt_irrefl _)
  · rfl

theorem getElem!_ofFn' {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {i : Nat}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem get_set! {A : Array Nat} {i v I : Nat} (hI : I < A.size) :
    (A.set! i v)[I]! = if i = I then v else A[I]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ I (by simpa using hI),
    Array.getElem_setIfInBounds hI, getElem!_pos A I hI]

theorem scatter_spec {N d : Nat} (g : Nat → Nat) : ∀ m : Nat,
    (∀ a < m, ∀ b < m, g a = g b → a = b) → (∀ k < m, g k < N) →
    ((List.range m).foldl (fun A k => A.set! (g k) k) (Array.replicate N d)).size = N ∧
    ∀ I < N, (∀ k < m, g k = I →
        ((List.range m).foldl (fun A k => A.set! (g k) k) (Array.replicate N d))[I]! = k) ∧
      ((∀ k < m, g k ≠ I) →
        ((List.range m).foldl (fun A k => A.set! (g k) k) (Array.replicate N d))[I]! = d)
  | 0, _, _ => by
    refine ⟨by simp, fun I hI => ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun _ => ?_⟩⟩
    rw [List.range_zero, List.foldl_nil, getElem!_pos _ I (by simpa using hI),
      Array.getElem_replicate]
  | m + 1, hinj, hlt => by
    obtain ⟨hs, ih⟩ := scatter_spec g m (fun a ha b hb => hinj a (by omega) b (by omega))
      (fun k hk => hlt k (by omega))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs], fun I hI =>
      ⟨fun k hk he => ?_, fun hne => ?_⟩⟩
    · rw [get_set! (by rw [hs]; exact hI)]
      by_cases hkm : k = m
      · rw [ite_eq_left (by rw [← hkm]; exact he), hkm]
      · have hne : g m ≠ I := fun e => hkm (hinj k hk m (by omega) (he.trans e.symm))
        rw [ite_eq_right hne]
        exact (ih I hI).1 k (by omega) he
    · rw [get_set! (by rw [hs]; exact hI), ite_eq_right (hne m (by omega))]
      exact (ih I hI).2 fun k hk => hne k (by omega)

theorem rec_line {L : Nat} (hL : L < 48) :
    fi22ExtInvRecLines[L]! = unpack 1920 20 (Fi22LabT.Rec.L L) := by
  have h := hexBind_sound Fi22LabT.Rec.all L hL
  rw [Nat.zero_add, ← Fi22LabT.Rec.eq] at h
  rw [fi22ExtInvRecLines, getElem!_ofFn' _ hL]
  exact h

theorem rec_get {k f : Nat} (hk : k < 6143) (hf : f < 15) : fi22ExtInvRec k f = RF k f := by
  rw [fi22ExtInvRec, rec_line (by omega), unpack_get' (by omega)]
  rfl

theorem sv_mono : ∀ b, b < 6143 → ∀ a < b, SV a < SV b
  | 0, _, a, ha => absurd ha (Nat.not_lt_zero a)
  | b + 1, hb, a, ha => by
    have h := (inv_parts (k := b) (by omega)).2.2 hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h' | h'
    · exact (sv_mono b (by omega) a h').trans h
    · rw [h']
      exact h

theorem pos_get {I : Nat} (hI : I < 262144) : fi22ExtInvPos[I]! = PP I := by
  have hs := (scatter_spec (N := 262144) (d := 6143) (fun k => fi22ExtInvRec k 14) 6143
    (fun a ha b hb e => by
      rw [rec_get ha (by norm_num), rec_get hb (by norm_num)] at e
      rcases Nat.lt_trichotomy a b with h | h | h
      · exact absurd e (sv_mono b hb a h).ne
      · exact h
      · exact absurd e (sv_mono a ha b h).ne')
    (fun k hk => by rw [rec_get hk (by norm_num)]; exact (inv_parts hk).2.1)).2 I hI
  cases e : isInvK I
  · rw [row_noinv hI e]
    refine hs.2 fun k hk he => ?_
    have h1 := (inv_parts hk).1
    change fi22ExtInvRec k 14 = I at he
    rw [rec_get hk (by norm_num)] at he
    change PP (RF k 14) = k at h1
    rw [he, row_noinv hI e] at h1
    omega
  · obtain ⟨hp, hsv, -⟩ := row_inv hI e
    refine hs.1 (PP I) hp ?_
    rw [rec_get hp (by norm_num)]
    exact hsv

theorem field_get {f d I : Nat} (hf : f < 15) (hI : I < 262144) :
    fi22ExtInvField f d I = nIf(Nat.blt (PP I) 6143, RF (PP I) f, d) := by
  unfold fi22ExtInvField
  rw [pos_get hI]
  by_cases h : PP I < 6143
  · rw [ite_eq_left h, rec_get h hf, show Nat.blt (PP I) 6143 = true from Eq.mpr Nat.blt_eq h]
  · rw [ite_eq_right h, show Nat.blt (PP I) 6143 = false from
      Bool.eq_false_iff.2 fun e => h (Nat.blt_eq ▸ e)]

theorem lab_get {I : Nat} (hI : I < 262144) : fi22ExtLabelsRec.lab[I]! = labOf I := by
  unfold fi22ExtLabelsRec
  dsimp only
  rw [getElem!_ofFn' _ hI]
  dsimp only
  rw [field_get (by norm_num) hI, labOf, strictN_eq']
  rfl

theorem dep_get {I : Nat} (hI : I < 262144) : fi22ExtLabelsRec.dep[I]! = depOf I := by
  unfold fi22ExtLabelsRec
  dsimp only
  rw [getElem!_ofFn' _ hI]
  dsimp only
  rw [field_get (by norm_num) hI, depOf, strictN_eq']
  rfl

theorem par_get {I : Nat} (hI : I < 262144) (h : PP I < 6143) :
    fi22ExtLabelsRec.par[I]! = PR (PP I) := by
  unfold fi22ExtLabelsRec
  dsimp only
  rw [getElem!_ofFn' _ hI]
  dsimp only
  rw [field_get (by norm_num) hI, show Nat.blt (PP I) 6143 = true from Eq.mpr Nat.blt_eq h]
  rfl

theorem gen_get {I : Nat} (hI : I < 262144) (h : PP I < 6143) :
    fi22ExtLabelsRec.gen[I]! = GN (PP I) := by
  unfold fi22ExtLabelsRec
  dsimp only
  rw [getElem!_ofFn' _ hI]
  dsimp only
  rw [field_get (by norm_num) hI, show Nat.blt (PP I) 6143 = true from Eq.mpr Nat.blt_eq h]
  rfl

theorem nb_get {I s : Nat} (hI : I < 262144) (hs : s < 10) (h : PP I < 6143) :
    fi22ExtLabelsRec.nb[I * 10 + s]! = NB (PP I * 10 + s) := by
  have e1 : (I * 10 + s) / 10 = I := by omega
  have e2 : (I * 10 + s) % 10 = s := by omega
  have e3 : Nat.div (PP I * 10 + s) 10 = PP I := by
    change (PP I * 10 + s) / 10 = PP I
    omega
  have e4 : Nat.add 4 (Nat.mod (PP I * 10 + s) 10) = 4 + s := by
    change 4 + (PP I * 10 + s) % 10 = 4 + s
    omega
  rw [NB, e3, e4]
  unfold fi22ExtLabelsRec
  dsimp only
  rw [getElem!_ofFn' _ (by omega)]
  dsimp only
  rw [e1, e2, field_get (by omega) hI, show Nat.blt (PP I) 6143 = true from Eq.mpr Nat.blt_eq h]

section Elements

theorem tr_lt {o k y : Nat} (hk : Nat.add o k < 1060) (hy : y < 3510) : tr o k y < 3510 :=
  cn_lt (tr_cn hk) y hy

theorem tlev {i k : Nat} (hi : i < 3) (hk : k < rcnt (Fi22TC.LR i)) :
    fi22TLevels[i]!.tr[k]! =
      unpack 3510 12 (Fi22TC.TR (Nat.add (roff 3510 (3510 * 12) (Fi22TC.LR i)) k)) := by
  have h := (levelTr_sound Fi22X.bindsT Fi22TC.head Fi22TC.hl (i := i) (by omega)).2 k hk
  rw [fi22TLevels]
  exact h

theorem tr3_eq {a b c p : Nat} (ha : a < 1024) (hb : b < 32) (hc : c < 4) (hp : p < 3510) :
    tr3 fi22TLevels a b c p = tr 0 a (tr 1024 b (tr 1056 c p)) := by
  obtain ⟨o0, o1, o2, c0, c1, c2⟩ := offs_parts
  have h2 := tlev (i := 2) (k := c) (by norm_num) (by rw [c2]; exact hc)
  have h1 := tlev (i := 1) (k := b) (by norm_num) (by rw [c1]; exact hb)
  have h0 := tlev (i := 0) (k := a) (by norm_num) (by rw [c0]; exact ha)
  rw [o2] at h2
  rw [o1] at h1
  rw [o0] at h0
  have l2 : tr 1056 c p < 3510 := tr_lt (by rw [Nat.add_eq]; omega) hp
  have l1 : tr 1024 b (tr 1056 c p) < 3510 := tr_lt (by rw [Nat.add_eq]; omega) l2
  unfold tr3
  rw [h2, unpack_get' hp]
  change (fi22TLevels[0]!.tr[a]!)[(fi22TLevels[1]!.tr[b]!)[tr 1056 c p]!]! = _
  rw [h1, unpack_get' l2]
  change (fi22TLevels[0]!.tr[a]!)[tr 1024 b (tr 1056 c p)]! = _
  rw [h0, unpack_get' l1]
  rfl

theorem qi_eq :fi22ExtQiArr = unpack 3510 12 (LI 0) := by
  rw [fi22ExtQiArr, Fi22E2067.ext_eq (L := 0) (by norm_num)]
  exact (invEqK_sound (Fi22E2067.perm3510 (L := 0) (by norm_num))).1

noncomputable abbrev Dp (t : Nat) (ht : t < 6) : Fin 3510 :=
  fi22ExtDeltaPt ⟨bs t, by interval_cases t <;> decide⟩

theorem perm_val {P : Nat} {G : Equiv.Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 P) G)
    (y : Fin 3510) : (G y : Nat) = pg 12 (mask 12) P y.val := by
  rw [← h y, unpack_get' y.2]

theorem conj_apply {H : Subgroup (Equiv.Perm (Fin 3510))} (a b : H) (x : Fin 3510) :
    ((a * b * a⁻¹ : H) : Equiv.Perm (Fin 3510)) x =
      (a : Equiv.Perm (Fin 3510)) ((b : Equiv.Perm (Fin 3510)) ((a : Equiv.Perm (Fin 3510))⁻¹ x)) :=
  rfl

theorem steps_size :fi22ExtSteps.size = 10 := by
  rw [fi22ExtSteps, Array.size_ofFn]

theorem labOf_inv {J : Nat} (h : PP J < 6143) : labOf J = LB (PP J) := by
  rw [labOf, strictN_eq', show Nat.blt (PP J) 6143 = true from Eq.mpr Nat.blt_eq h]

theorem labOf_noinv {J : Nat} (h : PP J = 6143) : labOf J = 79 := by
  rw [labOf, strictN_eq', h]
  rfl

theorem depOf_inv {J : Nat} (h : PP J < 6143) : depOf J = DE (PP J) := by
  rw [depOf, strictN_eq', show Nat.blt (PP J) 6143 = true from Eq.mpr Nat.blt_eq h]

theorem roots_size : fi22ExtRootsRec.size = 79 := by simp [fi22ExtRootsRec]

theorem pp_inv {I : Nat} (hI : I < 262144) (h : PP I < 6143) : SV (PP I) = I :=
  (row_inv hI (pp_lt_inv hI h)).2.1

theorem labOf_lt {I : Nat} (hI : I < 262144) (h : labOf I < 79) : PP I < 6143 := by
  by_contra hc
  have hp : PP I = 6143 := by
    have := row_noinv hI (by
      cases e : isInvK I
      · rfl
      · exact absurd (row_inv hI e).1 hc)
    exact this
  rw [labOf_noinv hp] at h
  exact lt_irrefl _ h

theorem labCnt_eq (j : Nat) : (List.range 6143).countP (fun k => LB k == j) = labCnt j := by
  unfold labCnt
  refine countP_range_rec (f := fun k => LB k == j) (g := fun k => Nat.beq (LB k) j) 6143
    fun k _ => ?_
  cases h : Nat.beq (LB k) j
  · exact beq_eq_false_iff_ne.2 fun e => by rw [e, Nat.beq_refl] at h; exact Bool.noConfusion h
  · exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)

theorem labCount_ok {j : Nat} (hj : j < 79) :
    labCount fi22ExtLabelsRec.lab 262144 j = fi22ExtClassSizes.getD j 0 := by
  unfold labCount
  rw [countP_range_eq (M := 6143) (g := fun k => LB k == j) PP SV, labCnt_eq,
    Nat.eq_of_beq_eq_true (allN_spec classCounts j hj)]
  · intro I hI hf
    rw [beq_iff_eq, lab_get hI] at hf
    have hp := labOf_lt hI (by rw [hf]; exact hj)
    rw [labOf_inv hp] at hf
    exact ⟨hp, beq_iff_eq.2 hf, pp_inv hI hp⟩
  · intro k hk hg
    obtain ⟨h1, h2, -⟩ := inv_parts hk
    refine ⟨h2, ?_, h1⟩
    rw [beq_iff_eq, lab_get h2, labOf_inv (by rw [h1]; exact hk), h1]
    exact beq_iff_eq.1 hg

theorem labelled_ok :labelledCount fi22ExtLabelsRec.lab 262144 79 = 6143 := by
  unfold labelledCount
  rw [countP_range_eq (M := 6143) (g := fun _ => true) PP SV]
  · simp
  · intro I hI hf
    rw [decide_eq_true_eq, lab_get hI] at hf
    have hp := labOf_lt hI hf
    exact ⟨hp, rfl, pp_inv hI hp⟩
  · intro k hk _
    obtain ⟨h1, h2, -⟩ := inv_parts hk
    have hp : PP (SV k) < 6143 := by rw [h1]; exact hk
    have hl := (row_inv h2 (pp_lt_inv h2 hp)).2.2.1
    rw [h1] at hl
    refine ⟨h2, ?_, h1⟩
    rw [decide_eq_true_eq, lab_get h2, labOf_inv hp, h1]
    exact hl

theorem fi22InP_eq {p : Nat} {g : Array Nat} (hg : g = unpack 3510 12 p) (hc : Fi22X.cn p = true) :
    fi22InP g = Fi22X.siftP p := by
  rw [fi22InP, siftK_eq Fi22X.bindsP Fi22X.permP Fi22PC.hl hg (Fi22X.hi_of hc)
    (range_of_canonK hc)]
  rfl

theorem gc_lt :∀ j < 79, fi22ExtGlobalClasses.getD j 0 < 6 := by decide

theorem conj_parts {j : Nat} (hj : j < 79) : Fi22X.cn (Fi22ExtT.L (106 + j)) = true ∧
    Fi22X.siftP (Fi22ExtT.L (106 + j)) = true ∧ Fi22X.cn (Fi22ExtT.L (27 + j)) = true ∧
    Fi22X.cn (Fi22ExtT.L (21 + fi22ExtGlobalClasses.getD j 0)) = true ∧
    Nat.beq (Fi22X.c (Fi22ExtT.L (106 + j)) (Fi22ExtT.L (27 + j)))
      (Fi22X.c (Fi22ExtT.L (21 + fi22ExtGlobalClasses.getD j 0)) (Fi22ExtT.L (106 + j))) =
        true := by
  have h := conj_at hj
  unfold conjRow memP at h
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := by simpa only [bAnd_iff] using h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem h_ok {j : Nat} (hj : j < 79) : fi22InP (fi22ExtArr (106 + j)) = true ∧
    eqA 3510 (compA 3510 (fi22ExtArr (106 + j)) (fi22ExtArr (27 + j)))
      (compA 3510 (fi22ExtArr (21 + fi22ExtGlobalClasses.getD j 0)) (fi22ExtArr (106 + j))) =
        true := by
  obtain ⟨c1, s1, c2, c3, he⟩ := conj_parts hj
  have hg := gc_lt j hj
  refine ⟨by rw [fi22InP_eq (Fi22E2067.ext_eq (by omega)) c1]; exact s1, ?_⟩
  rw [Fi22E2067.ext_eq (L := 106 + j) (by omega), Fi22E2067.ext_eq (L := 27 + j) (by omega),
    Fi22E2067.ext_eq (L := 21 + fi22ExtGlobalClasses.getD j 0) (by omega), Fi22X.comp_eq c1 c2,
    Fi22X.comp_eq c3 c1]
  exact Fi22X.eqA_of (Fi22X.cn_c c1 c2) (Fi22X.cn_c c3 c1) he

theorem rep_facts :
    (∀ i < 3, Fi22ExtT.L (21 + i) = O6 i) ∧ Fi22ExtT.L 24 = Fi22X.GO ∧
    (∀ k < 6, neIdK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) (Fi22ExtT.L (21 + k)) = true ∧
      sqIdK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) (Fi22ExtT.L (21 + k)) = true) ∧
    fixK (Fi22ExtT.L 21) = 54 ∧ fixK (Fi22ExtT.L 22) = 182 ∧ fixK (Fi22ExtT.L 23) = 694 ∧
    fixK (Fi22ExtT.L 24) = 72 ∧ fixK (Fi22ExtT.L 25) = 360 ∧ fixK (Fi22ExtT.L 26) = 64 ∧
    (∀ k < 3, Fi22X.cn (Fi22ExtT.L (21 + k)) = true ∧ Fi22X.siftP (Fi22ExtT.L (21 + k)) = true) ∧
    (∀ k < 3, Fi22X.cn (Fi22ExtT.L (24 + k)) = true ∧ Fi22X.siftP (Fi22ExtT.L (24 + k)) = false ∧
      Fi22X.cn (Fi22X.c Fi22X.GO (Fi22ExtT.L (24 + k))) = true ∧
      Fi22X.siftP (Fi22X.c Fi22X.GO (Fi22ExtT.L (24 + k))) = true) := by
  obtain ⟨a, b, c, d1, d2, d3, d4, d5, d6, e, f⟩ := by simpa only [bAnd_iff] using repFacts
  refine ⟨fun i hi => Nat.eq_of_beq_eq_true (allN_spec a i hi), Nat.eq_of_beq_eq_true b,
    fun k hk => (bAnd_iff _ _).1 (allN_spec c k hk), Nat.eq_of_beq_eq_true d1,
    Nat.eq_of_beq_eq_true d2, Nat.eq_of_beq_eq_true d3, Nat.eq_of_beq_eq_true d4,
    Nat.eq_of_beq_eq_true d5, Nat.eq_of_beq_eq_true d6,
    fun k hk => (bAnd_iff _ _).1 (allN_spec e k hk), fun k hk => ?_⟩
  obtain ⟨g1, g2, g3, g4⟩ := by simpa only [bAnd_iff] using allN_spec f k hk
  refine ⟨g1, ?_, g3, g4⟩
  change Fi22X.siftP (Lx (Nat.add 24 k)) = false
  cases e2 : Fi22X.siftP (Lx (Nat.add 24 k))
  · rfl
  · rw [e2] at g2
    exact Bool.noConfusion g2

theorem out6_eq {i : Nat} (hi : i < 3) : (fi22OuterStrong3510 6)[i]! = unpack 3510 12 (O6 i) := by
  have hl : fi22OuterLine3510 6 i = 36 + i := by
    unfold fi22OuterLine3510
    simp [fi22OuterLines3510]
  unfold fi22OuterStrong3510
  rw [getElem!_pos _ i (by simpa [fi22OuterLines3510] using hi), Array.getElem_ofFn]
  change fi22OuterArr3510 (fi22OuterLine3510 6 i) = _
  rw [hl]
  have hk : outL i = true := by
    match i, hi with
    | 0, _ => exact out6l0
    | 1, _ => exact out6l1
    | 2, _ => exact out6l2
  exact Fi22X.line_of Fi22OutT.eq (Fi22X.asciiK_take out6a (by simp only [Nat.mul_eq]; omega)) hk

theorem eqA_refl' {a : Array Nat} : eqA 3510 a a = true := eqA_of_get fun _ _ => rfl

theorem outer_ok :
    (∀ i < 3, eqA 3510 (fi22ExtArr (21 + i)) (fi22OuterStrong3510 6)[i]! = true) ∧
    eqA 3510 (fi22ExtArr 24) fi22GraphOuterArr = true ∧
    (∀ k < 6, isInvArr 3510 (fi22ExtArr (21 + k)) = true) ∧
    ((List.range 6).map fun k => fixCount 3510 (fi22ExtArr (21 + k))) =
      [54, 182, 694, 72, 360, 64] ∧
    (∀ k < 3, fi22InP (fi22ExtArr (21 + k)) = true) ∧
    (∀ k < 3, fi22InP (fi22ExtArr (24 + k)) = false ∧
      fi22InP (compA 3510 fi22GraphOuterArr (fi22ExtArr (24 + k))) = true) := by
  obtain ⟨h6, h24, hinv, f1, f2, f3, f4, f5, f6, hP, hQ⟩ := rep_facts
  refine ⟨fun i hi => ?_, ?_, fun k hk => ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [Fi22E2067.ext_eq (by omega), out6_eq hi, ← h6 i hi]
    exact eqA_refl'
  · rw [Fi22E2067.ext_eq (by norm_num), Fi22X.go_eq, ← h24]
    exact eqA_refl'
  · obtain ⟨a, b⟩ := hinv k hk
    unfold isInvArr
    rw [Fi22E2067.ext_eq (by omega), neIdK_sound a, sqIdK_sound b]
    rfl
  · have e : ∀ L, L < 185 → fixCount 3510 (fi22ExtArr L) = fixK (Fi22ExtT.L L) := fun L hL => by
      rw [Fi22E2067.ext_eq hL, fixCount_eq]
    rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [e 21 (by norm_num), e 22 (by norm_num), e 23 (by norm_num), e 24 (by norm_num),
      e 25 (by norm_num), e 26 (by norm_num), f1, f2, f3, f4, f5, f6]
  · obtain ⟨a, b⟩ := hP k hk
    rw [fi22InP_eq (Fi22E2067.ext_eq (by omega)) a]
    exact b
  · obtain ⟨a, b, c, d⟩ := hQ k hk
    refine ⟨by rw [fi22InP_eq (Fi22E2067.ext_eq (by omega)) a]; exact b, ?_⟩
    rw [Fi22X.go_eq, Fi22E2067.ext_eq (by omega), Fi22X.comp_eq Fi22X.cnG a, fi22InP_eq rfl c]
    exact d

theorem steps_ok {k : Nat} (hk : k < 10) :
    isInvA 256 fi22ExtSteps[k]! fi22ExtStepsInv[k]! = true := by
  rw [fi22ExtSteps_get hk, fi22ExtStepsInv_get hk]
  exact Fi22E2067.isInv_of (Fi22E2067.ext256_eq (by omega))
    (allN_spec Fi22E2067.perm256 k (by omega))

end Elements

end CertificateChecks.KernelSpor.Fi22LabA

end
