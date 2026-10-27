module

public import Certificates.Kernel.SporSch.Tits.Syl8117E
public import Certificates.Kernel.SporSch.Tits.Syl8117G
public import Certificates.Kernel.SporSch.Tits.Inv2266
public import Certificates.Kernel.SporSch.Tits.Stab2270
public import CFSG.Certificates.Kernel.SporSch.TitsSylSound
public import CFSG.Sporadic.Schreier.TitsDAction
public import CFSG.Sporadic.Schreier.TitsStab
public import CFSG.Sporadic.Schreier.TitsInv
public import CFSG.Sporadic.Schreier.TitsEnum
public import CFSG.Sporadic.Schreier.TitsCentral
public import CFSG.Sporadic.Schreier.TitsCentralCheck
public import CFSG.Sporadic.Schreier.TitsLocalCheck
public import CFSG.Certificates.Kernel.LocalQTCovTPrim
public import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.RankThree.PartTwo.Sec4.Item434RemTits
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel
open CertificateChecks.KernelSporSch.Heis3 CFSG.KC.PkPow

theorem bnd {n w P : Nat} {σ : Equiv.Perm (Fin n)} (h : Rep n (unpack n w P) σ) :
    ∀ i < n, pg w (mask w) P i < n := fun i hi => by
  have := h.lt hi
  rwa [CFSG.KS.Raw.Orb.unpack_get hi] at this

theorem repP {n w P Q : Nat} (hn : n < 2 ^ 32) {σ τ : Equiv.Perm (Fin n)}
    (hP : Rep n (unpack n w P) σ) (hQ : Rep n (unpack n w Q) τ) :
    Rep n (unpack n w (pcomp n w (mask w) P Q)) (σ * τ) := by
  rw [← CFSG.KC.LQT.Cov.T.compA_unpack hn (bnd hQ)]
  exact rep_compA hP hQ

theorem band {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem eqP {n w P Q : Nat} {σ τ : Equiv.Perm (Fin n)} (hP : Rep n (unpack n w P) σ)
    (hQ : Rep n (unpack n w Q) τ) (h : Nat.beq P Q = true) : σ = τ := by
  rw [Nat.eq_of_beq_eq_true h] at hP
  exact hP.unique hQ

theorem canonP {P Q : Nat} {σ τ : Equiv.Perm (Fin 1755)} (hP : Rep 1755 (unpack 1755 11 P) σ)
    (hQ : Rep 1755 (unpack 1755 11 Q) τ) :
    canonK 1755 11 (mask 11) (1755 * 11) (pcomp 1755 11 (mask 11) P Q) = true := by
  have hr := bnd (repP (by norm_num) hP hQ)
  unfold canonK szOK
  rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq]
  refine ⟨⟨by norm_num, by decide⟩, PackFld.pcomp_shr (by norm_num) (by norm_num),
    PackFld.allN_of_forall fun i hi => Nat.blt_eq.mpr (hr i hi)⟩

theorem neP {P Q P' Q' : Nat} {σ τ σ' τ' : Equiv.Perm (Fin 1755)}
    (hP : Rep 1755 (unpack 1755 11 P) σ) (hQ : Rep 1755 (unpack 1755 11 Q) τ)
    (hP' : Rep 1755 (unpack 1755 11 P') σ') (hQ' : Rep 1755 (unpack 1755 11 Q') τ')
    (h : bIf(Nat.beq (pcomp 1755 11 (mask 11) P Q) (pcomp 1755 11 (mask 11) P' Q'), false, true) =
      true) : σ * τ ≠ σ' * τ' := by
  intro e
  have he := (eqA_iff (repP (by norm_num) hP hQ) (repP (by norm_num) hP' hQ')).2 e
  rw [eqA_unpack (canonP hP hQ) (canonP hP' hQ')] at he
  rw [he] at h
  exact absurd h (by decide)

theorem id_rep : Rep 1755 (unpack 1755 11 (pidn 1755 11)) 1 := by
  rw [CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num)]
  exact rep_idA

theorem wordK_eq {wd : List Int} (hl : lettersK 13 wd = true) :
    wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 wd (wK wd) = true := by
  have e : Nat.beq (wordK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI wd) (wK wd) = true :=
    Nat.beq_refl _
  unfold wordEqK
  rw [hl, e] <;> rfl

theorem repD {wd : List Int} (hl : lettersK 13 wd = true) :
    Rep 1755 (unpack 1755 11 (wK wd)) (wordIn 13 titsT wd) := by
  rw [← wa_eq (wordK_eq hl)]
  exact rep_wordArr_titsT (lettersK_sound hl)

theorem wordIn_nil {G : Type*} [Group G] (k : ℕ) (gs : ℕ → G) : wordIn k gs [] = 1 := by
  simp [wordIn, toLetters]

theorem wordIn_powWord {G : Type*} [Group G] (k : ℕ) (gs : ℕ → G) (w : List ℤ) :
    ∀ n, wordIn k gs (powWord w n) = wordIn k gs w ^ n
  | 0 => by rw [pow_zero, ← wordIn_nil k gs]; rfl
  | n + 1 => by
    rw [pow_succ', ← wordIn_powWord k gs w n, ← wordIn_append]
    rfl

theorem wordIn_neg {G : Type*} [Group G] (k : ℕ) (gs : ℕ → G) (l : ℤ) :
    wordIn k gs [-l] = (wordIn k gs [l])⁻¹ := by
  by_cases h : l ≠ 0 ∧ l.natAbs ≤ k
  · have h' : -l ≠ 0 ∧ (-l).natAbs ≤ k := by
      rw [Int.natAbs_neg]
      exact ⟨neg_ne_zero.2 h.1, h.2⟩
    rcases lt_or_gt_of_ne h.1 with hl | hl
    · have hl' : 0 < -l := by omega
      have hl'' : ¬ 0 < l := by omega
      simp [wordIn, toLetters, h, h', hl', hl, hl'', Int.natAbs_neg]
    · have hl' : ¬ 0 < -l := by omega
      simp [wordIn, toLetters, h, h', hl', hl, not_lt.2 hl.le, Int.natAbs_neg]
  · have h' : ¬ (-l ≠ 0 ∧ (-l).natAbs ≤ k) := by
      rw [Int.natAbs_neg, neg_ne_zero]
      exact h
    simp only [wordIn, toLetters, List.filterMap_cons, List.filterMap_nil, dif_neg h, dif_neg h']
    simp

@[expose] def invW (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

theorem wordIn_invW {G : Type*} [Group G] (k : ℕ) (gs : ℕ → G) :
    ∀ w : List ℤ, wordIn k gs (invW w) = (wordIn k gs w)⁻¹
  | [] => by rw [wordIn_nil]; exact (inv_one).symm
  | l :: w => by
    have e : invW (l :: w) = invW w ++ [-l] := by simp [invW]
    have e' : l :: w = [l] ++ w := rfl
    rw [e, wordIn_append, wordIn_invW k gs w, wordIn_neg, e', wordIn_append, mul_inv_rev]

@[expose] noncomputable def eD (w : List ℤ) : titsD :=
  ⟨wordIn 13 titsT w, wordIn_titsT_mem_titsD w⟩

theorem eD_append (v w : List ℤ) : eD (v ++ w) = eD v * eD w :=
  Subtype.ext (wordIn_append _ _ _ _)

theorem rel3_facts :
    wordIn 13 titsT xWord * (wordIn 13 titsT xWord * wordIn 13 titsT xWord) = 1 ∧
    wordIn 13 titsT yWord * (wordIn 13 titsT yWord * wordIn 13 titsT yWord) = 1 ∧
    wordIn 13 titsT zWord * (wordIn 13 titsT zWord * wordIn 13 titsT zWord) = 1 ∧
    wordIn 13 titsT xWord * wordIn 13 titsT yWord = wordIn 13 titsT yWord * wordIn 13 titsT xWord ∧
    wordIn 13 titsT xWord * wordIn 13 titsT zWord = wordIn 13 titsT zWord * wordIn 13 titsT xWord ∧
    (wordIn 13 titsT yWord * wordIn 13 titsT zWord =
        wordIn 13 titsT xWord * (wordIn 13 titsT zWord * wordIn 13 titsT yWord) ∨
      wordIn 13 titsT yWord * wordIn 13 titsT zWord = wordIn 13 titsT xWord *
        wordIn 13 titsT xWord * (wordIn 13 titsT zWord * wordIn 13 titsT yWord)) ∧
    wordIn 13 titsT yWord * wordIn 13 titsT zWord ≠
      wordIn 13 titsT zWord * wordIn 13 titsT yWord := by
  have h := rels
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  unfold rel3 at h
  rw [strictB_eq, strictB_eq] at h
  have rX := repD lX
  have rY := repD lY
  have rZ := repD lZ
  have hn : (1755 : Nat) < 2 ^ 32 := by norm_num
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨eqP (repP hn rX (repP hn rX rX)) id_rep h1, eqP (repP hn rY (repP hn rY rY)) id_rep h2,
    eqP (repP hn rZ (repP hn rZ rZ)) id_rep h3, eqP (repP hn rX rY) (repP hn rY rX) h4,
    eqP (repP hn rX rZ) (repP hn rZ rX) h5, ?_, neP rY rZ rZ rY h7⟩
  cases e : Nat.beq (pcomp 1755 11 (mask 11) (wK yWord) (wK zWord))
      (pcomp 1755 11 (mask 11) (wK xWord) (pcomp 1755 11 (mask 11) (wK zWord) (wK yWord)))
  · rw [e] at h6
    exact Or.inr (eqP (repP hn rY rZ) (repP hn (repP hn rX rX) (repP hn rZ rY)) h6)
  · exact Or.inl (eqP (repP hn rY rZ) (repP hn rX (repP hn rZ rY)) e)

theorem rel3D :
    ∃ j, Rel3 (eD xWord) (eD yWord) (eD zWord) j := by
  obtain ⟨c1, c2, c3, cxy, cxz, cyz, hne⟩ := rel3_facts
  have p3 : ∀ w : List ℤ, wordIn 13 titsT w * (wordIn 13 titsT w * wordIn 13 titsT w) = 1 →
      eD w ^ 3 = 1 := fun w h => Subtype.ext (by
    rw [Subgroup.coe_pow, pow_three]
    exact h)
  have x1 : eD xWord ≠ 1 := fun e => hne (by
    have e' : wordIn 13 titsT xWord = 1 := congrArg Subtype.val e
    rcases cyz with h | h <;> rw [h, e'] <;> simp)
  have hx3 : wordIn 13 titsT xWord ^ 3 = 1 := by rw [pow_three]; exact c1
  rcases cyz with h | h
  · refine ⟨2, p3 _ c1, p3 _ c2, p3 _ c3, Subtype.ext cxy, Subtype.ext cxz, Subtype.ext ?_,
      Or.inr rfl, x1⟩
    change wordIn 13 titsT zWord * wordIn 13 titsT yWord = wordIn 13 titsT xWord ^ 2 *
      (wordIn 13 titsT yWord * wordIn 13 titsT zWord)
    rw [h, ← mul_assoc, ← pow_succ, hx3, one_mul]
  · refine ⟨1, p3 _ c1, p3 _ c2, p3 _ c3, Subtype.ext cxy, Subtype.ext cxz, Subtype.ext ?_,
      Or.inl rfl, x1⟩
    change wordIn 13 titsT zWord * wordIn 13 titsT yWord = wordIn 13 titsT xWord ^ 1 *
      (wordIn 13 titsT yWord * wordIn 13 titsT zWord)
    rw [h, pow_one, ← mul_assoc, c1, one_mul]

@[expose] def tk (k : ℕ) : ℕ × ℕ × ℕ := (k / 9, k / 3 % 3, k % 3)

theorem tk_bd (k : ℕ) (hk : k < 27) : Bd (tk k) :=
  ⟨by simp only [tk]; omega, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem tk_inj {k k' : ℕ} (hk : k < 27) (hk' : k' < 27) (h : tk k = tk k') : k = k' := by
  simp only [tk, Prod.mk.injEq] at h
  omega

theorem tk_surj {t : ℕ × ℕ × ℕ} (ht : Bd t) : ∃ k < 27, tk k = t := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨ha, hb, hc⟩ : a < 3 ∧ b < 3 ∧ c < 3 := ht
  refine ⟨9 * a + 3 * b + c, by omega, ?_⟩
  simp only [tk, Prod.mk.injEq]
  omega

theorem mem_sylWords {w : List ℤ} : w ∈ sylWords ↔ ∃ k < 27, powWord xWord (tk k).1 ++
    powWord yWord (tk k).2.1 ++ powWord zWord (tk k).2.2 = w := by
  simp [sylWords, tk, List.mem_map, List.mem_range]

theorem eD_tk (k : ℕ) :
    eD (powWord xWord (tk k).1 ++ powWord yWord (tk k).2.1 ++ powWord zWord (tk k).2.2) =
      f (eD xWord) (eD yWord) (eD zWord) (tk k) := by
  rw [eD_append, eD_append]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;> exact Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact wordIn_powWord _ _ _ _)

theorem wordIn_tk (k : ℕ) :
    wordIn 13 titsT (powWord xWord (tk k).1 ++ powWord yWord (tk k).2.1 ++
      powWord zWord (tk k).2.2) = (f (eD xWord) (eD yWord) (eD zWord) (tk k) : titsD) :=
  congrArg Subtype.val (eD_tk k)

theorem mem_syl {g : Equiv.Perm (Fin 1755)} :
    g ∈ sylWords.map (wordIn 13 titsT) ↔
      ∃ t, Bd t ∧ ((f (eD xWord) (eD yWord) (eD zWord) t : titsD) : Equiv.Perm (Fin 1755)) =
        g := by
  rw [List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := mem_sylWords.1 hw
    exact ⟨tk k, tk_bd k hk, (wordIn_tk k).symm⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨k, hk, rfl⟩ := tk_surj ht
    exact ⟨_, mem_sylWords.2 ⟨k, hk, rfl⟩, wordIn_tk k⟩

theorem syl_nodup : (sylWords.map (wordIn 13 titsT)).Nodup := by
  obtain ⟨j, R⟩ := rel3D
  have e : sylWords.map (wordIn 13 titsT) = (List.range 27).map fun k =>
      ((f (eD xWord) (eD yWord) (eD zWord) (tk k) : titsD) : Equiv.Perm (Fin 1755)) := by
    rw [sylWords, List.map_map]
    exact List.map_congr_left fun k _ => wordIn_tk k
  rw [e]
  refine (List.nodup_range).map_on fun k hk k' hk' h => ?_
  rw [List.mem_range] at hk hk'
  exact tk_inj hk hk' (f_inj R (tk_bd k hk) (tk_bd k' hk') (Subtype.ext h))

theorem syl_mul {g h : Equiv.Perm (Fin 1755)}
    (hg : g ∈ sylWords.map (wordIn 13 titsT)) (hh : h ∈ sylWords.map (wordIn 13 titsT)) :
    g * h ∈ sylWords.map (wordIn 13 titsT) := by
  obtain ⟨j, R⟩ := rel3D
  obtain ⟨t, -, rfl⟩ := mem_syl.1 hg
  obtain ⟨s, -, rfl⟩ := mem_syl.1 hh
  exact mem_syl.2 ⟨mulT j t s, bd_mulT t s, by rw [← f_mul R]; rfl⟩

theorem syl_cube {g : Equiv.Perm (Fin 1755)}
    (hg : g ∈ sylWords.map (wordIn 13 titsT)) : g ^ 3 = 1 := by
  obtain ⟨j, R⟩ := rel3D
  obtain ⟨t, ht, rfl⟩ := mem_syl.1 hg
  rw [← Subgroup.coe_pow, pow_three, f_cube R ht]
  rfl

theorem syl_noncomm :
    ∃ g ∈ sylWords.map (wordIn 13 titsT), ∃ h ∈ sylWords.map (wordIn 13 titsT), g * h ≠ h * g := by
  obtain ⟨j, R⟩ := rel3D
  have ey : f (eD xWord) (eD yWord) (eD zWord) (0, 1, 0) = eD yWord := by simp [f]
  have ez : f (eD xWord) (eD yWord) (eD zWord) (0, 0, 1) = eD zWord := by simp [f]
  have b1 : Bd (0, 1, 0) := ⟨by norm_num, by norm_num, by norm_num⟩
  have b2 : Bd (0, 0, 1) := ⟨by norm_num, by norm_num, by norm_num⟩
  refine ⟨_, mem_syl.2 ⟨(0, 1, 0), b1, rfl⟩, _, mem_syl.2 ⟨(0, 0, 1), b2, rfl⟩,
    fun e => yz_ne R ?_⟩
  rw [ey, ez] at e
  exact Subtype.ext e

@[expose] def LC (σ : Equiv.Perm (Fin 2925)) : Prop :=
  ¬ 5 ∣ Fintype.card {p : Fin 2925 // σ p = p} ∧ ¬ 13 ∣ Fintype.card {p : Fin 2925 // σ p = p}

theorem card_fix_conj (τ σ : Equiv.Perm (Fin 2925)) :
    Fintype.card {p : Fin 2925 // (τ * σ * τ⁻¹) p = p} = Fintype.card {p : Fin 2925 // σ p = p} :=
  Fintype.card_congr (Equiv.subtypeEquiv τ⁻¹ fun p => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.eq_inv_iff_eq])

theorem card_fix_inv (σ : Equiv.Perm (Fin 2925)) :
    Fintype.card {p : Fin 2925 // σ⁻¹ p = p} = Fintype.card {p : Fin 2925 // σ p = p} :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun p => Equiv.Perm.inv_eq_iff_eq.trans eq_comm)

theorem LC_conj {τ σ : Equiv.Perm (Fin 2925)} : LC (τ * σ * τ⁻¹) ↔ LC σ := by
  rw [LC, LC, card_fix_conj]

theorem LC_inv {σ : Equiv.Perm (Fin 2925)} : LC σ⁻¹ ↔ LC σ := by
  rw [LC, LC, card_fix_inv]

theorem nfix_count (n w P : Nat) :
    nfix n w P = (List.range n).countP fun x => Nat.beq (pg w (mask w) P x) x := by
  unfold nfix
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP]
  induction (List.range n) with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.countP_cons]
    cases Nat.beq (pg w (mask w) P x) x <;> rfl

theorem card_fix_nfix {P : Nat} {σ : Equiv.Perm (Fin 2925)} (h : Rep 2925 (unpack 2925 12 P) σ) :
    Fintype.card {p : Fin 2925 // σ p = p} = nfix 2925 12 P := by
  have hl : nfix 2925 12 P = (List.finRange 2925).countP fun x => decide (σ x = x) := by
    rw [nfix_count, ← List.map_coe_finRange_eq_range, List.countP_map]
    congr 1
    funext x
    rw [Function.comp_apply, Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff,
      ← CFSG.KS.Raw.Orb.unpack_get x.2, h x, Fin.ext_iff]
  rw [hl, Fintype.card_subtype, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange 2925).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  simp

theorem LC_of {P : Nat} {σ : Equiv.Perm (Fin 2925)} (h : Rep 2925 (unpack 2925 12 P) σ)
    (hp : p513 (nfix 2925 12 P) = true) : LC σ := by
  rw [LC, card_fix_nfix h]
  unfold p513 at hp
  obtain ⟨h5, h13⟩ := band hp
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · have e : Nat.beq (Nat.mod (nfix 2925 12 P) 5) 0 = true := by
      rw [Nat.beq_eq]
      exact Nat.mod_eq_zero_of_dvd hd
    rw [e] at h5
    exact absurd h5 (by decide)
  · have e : Nat.beq (Nat.mod (nfix 2925 12 P) 13) 0 = true := by
      rw [Nat.beq_eq]
      exact Nat.mod_eq_zero_of_dvd hd
    rw [e] at h13
    exact absurd h13 (by decide)

theorem repS {wd : List Int}
    (hl : lettersK 13 wd = true) : Rep 2925 (unpack 2925 12 (wS wd)) (wordIn 13 titsTStar wd) := by
  have e : Nat.beq (wordK 2925 12 (mask 12) (pidn 2925 12) TitsSS.T TitsSS.TI wd) (wS wd) = true :=
    Nat.beq_refl _
  have hw : wordEqK 2925 12 (mask 12) (pidn 2925 12) TitsSS.T TitsSS.TI 13 wd (wS wd) = true := by
    unfold wordEqK
    rw [hl, e] <;> rfl
  have ha := (wordEqK_sound ⟨TitsStab.tS_size, fun _ hj => TitsStab.tS_get hj⟩ TitsStab.aTp' hw).1
  rw [← ha]
  exact rep_wordArr_tstar (lettersK_sound hl)

@[expose] noncomputable def ρ
    (g : titsD) : Equiv.Perm (Fin 2925) := titsDLineAct g

theorem ρ_eD
    (w : List ℤ) : ρ (eD w) = wordIn 13 titsTStar w :=
  titsDLineAct_word w

theorem LC_base :
    LC (ρ (eD xWord)) ∧ LC (ρ (eD yWord * eD zWord)) ∧
      LC (ρ (eD yWord * (eD zWord * eD zWord))) := by
  have h := lines
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  unfold lines3 at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have rX := repS lX
  have rY := repS lY
  have rZ := repS lZ
  have hn : (2925 : Nat) < 2 ^ 32 := by norm_num
  have m : ∀ g h : titsD, ρ (g * h) = ρ g * ρ h := fun g h => map_mul titsDLineAct g h
  rw [m, m, m, ρ_eD, ρ_eD, ρ_eD]
  exact ⟨LC_of rX h1, LC_of (repP hn rY rZ) h2, LC_of (repP hn rY (repP hn rZ rZ)) h3⟩

theorem yz_conj :
    eD yWord = eD [2, -12, 4, 5, -11, -2] * eD xWord * (eD [2, -12, 4, 5, -11, -2])⁻¹ ∧
    eD zWord = eD [-11, -2, -3, -6] * eD xWord * (eD [-11, -2, -3, -6])⁻¹ := by
  have e1 : (eD [2, -12, 4, 5, -11, -2])⁻¹ = eD [2, 11, -5, -4, 12, -2] :=
    Subtype.ext (by
      rw [Subgroup.coe_inv]
      exact (wordIn_invW 13 titsT [2, -12, 4, 5, -11, -2]).symm)
  have e2 : (eD [-11, -2, -3, -6])⁻¹ = eD [6, 3, 2, 11] :=
    Subtype.ext (by
      rw [Subgroup.coe_inv]
      exact (wordIn_invW 13 titsT [-11, -2, -3, -6]).symm)
  rw [e1, e2, ← eD_append, ← eD_append, ← eD_append, ← eD_append]
  exact ⟨rfl, rfl⟩

@[expose] def tgts (j : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(1, 0, 0), (2, 0, 0), (0, 1, 0), (0, 2, 0), (0, 0, 1), (0, 0, 2), (0, 1, 1),
    mulT j (0, 1, 1) (0, 1, 1), (0, 1, 2), mulT j (0, 1, 2) (0, 1, 2)]

theorem conjB (j : ℕ) (hj : j = 1 ∨ j = 2) : (List.range 3).all (fun a => (List.range 3).all
    (fun b => (List.range 3).all (fun c => (a, b, c) == (0, 0, 0) ||
      (List.range 27).any (fun k => (tgts j).contains (conjT j (tk k) (a, b, c)))))) = true := by
  rcases hj with rfl | rfl <;> decide +kernel

theorem exists_conj {j : ℕ} (hj : j = 1 ∨ j = 2) {t : ℕ × ℕ × ℕ} (ht : Bd t)
    (h0 : t ≠ (0, 0, 0)) : ∃ k < 27, conjT j (tk k) t ∈ tgts j := by
  have h := conjB j hj
  obtain ⟨a, b, c⟩ := t
  obtain ⟨ha, hb, hc⟩ : a < 3 ∧ b < 3 ∧ c < 3 := ht
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
    List.contains_iff_mem] at h
  obtain h | ⟨k, hk, hk'⟩ := h a ha b hb c hc
  · exact absurd h h0
  · exact ⟨k, hk, hk'⟩

theorem LC_f
    {j : ℕ}
    (R : Rel3 (eD xWord) (eD yWord) (eD zWord) j) {t : ℕ × ℕ × ℕ} (ht : Bd t)
    (h1 : f (eD xWord) (eD yWord) (eD zWord) t ≠ 1) :
    LC (ρ (f (eD xWord) (eD yWord) (eD zWord) t)) := by
  have m : ∀ g h : titsD, ρ (g * h) = ρ g * ρ h := fun g h => map_mul titsDLineAct g h
  have mi : ∀ g : titsD, ρ g⁻¹ = (ρ g)⁻¹ := fun g => map_inv titsDLineAct g
  have hρc : ∀ s g : titsD, LC (ρ (s * g * s⁻¹)) ↔ LC (ρ g) := fun s g => by
    rw [m, m, mi]
    exact LC_conj
  have hρi : ∀ g : titsD, LC (ρ g⁻¹) ↔ LC (ρ g) := fun g => by
    rw [mi]
    exact LC_inv
  have h0 : t ≠ (0, 0, 0) := fun e => h1 (by rw [e]; exact f_zero)
  obtain ⟨k, hk, hr⟩ := exists_conj R.j12 ht h0
  rw [← hρc (f (eD xWord) (eD yWord) (eD zWord) (tk k)), f_conj R (tk_bd k hk)]
  obtain ⟨b1, b2, b3⟩ := LC_base
  obtain ⟨cy, cz⟩ := yz_conj
  have lx : LC (ρ (eD xWord)) := b1
  have ly : LC (ρ (eD yWord)) := by rw [cy, hρc]; exact lx
  have lz : LC (ρ (eD zWord)) := by rw [cz, hρc]; exact lx
  have sq : ∀ g : titsD, g ^ 3 = 1 → g * g = g⁻¹ := fun g hg =>
    eq_inv_of_mul_eq_one_left (a := g * g) (b := g) (by rw [← pow_three', hg])
  have p1 : ∀ s : ℕ × ℕ × ℕ, Bd s → LC (ρ (f (eD xWord) (eD yWord) (eD zWord) s)) →
      LC (ρ (f (eD xWord) (eD yWord) (eD zWord) (mulT j s s))) := fun s hs hl => by
    rw [← f_inv R hs, hρi]
    exact hl
  simp only [tgts, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with e | e | e | e | e | e | e | e | e | e <;> rw [e]
  · simpa [f] using lx
  · have : f (eD xWord) (eD yWord) (eD zWord) (2, 0, 0) = (eD xWord)⁻¹ := by
      simp only [f, pow_zero, mul_one]
      rw [pow_two, sq _ R.x3]
    rw [this, hρi]
    exact lx
  · simpa [f] using ly
  · have : f (eD xWord) (eD yWord) (eD zWord) (0, 2, 0) = (eD yWord)⁻¹ := by
      simp only [f, pow_zero, one_mul, mul_one]
      rw [pow_two, sq _ R.y3]
    rw [this, hρi]
    exact ly
  · simpa [f] using lz
  · have : f (eD xWord) (eD yWord) (eD zWord) (0, 0, 2) = (eD zWord)⁻¹ := by
      simp only [f, pow_zero, one_mul]
      rw [pow_two, sq _ R.z3]
    rw [this, hρi]
    exact lz
  · simpa [f] using b2
  · exact p1 (0, 1, 1) ⟨by norm_num, by norm_num, by norm_num⟩ (by simpa [f] using b2)
  · simpa [f, pow_two] using b3
  · exact p1 (0, 1, 2) ⟨by norm_num, by norm_num, by norm_num⟩ (by simpa [f, pow_two] using b3)

theorem syl_lines
    {w : List ℤ} (hw : w ∈ sylWords)
    (h1 : wordIn 13 titsT w ≠ 1) :
    ¬ 5 ∣ Fintype.card {p : Fin 2925 // wordIn 13 titsTStar w p = p} ∧
      ¬ 13 ∣ Fintype.card {p : Fin 2925 // wordIn 13 titsTStar w p = p} := by
  obtain ⟨j, R⟩ := rel3D
  obtain ⟨k, hk, rfl⟩ := mem_sylWords.1 hw
  have e := ρ_eD (powWord xWord (tk k).1 ++ powWord yWord (tk k).2.1 ++ powWord zWord (tk k).2.2)
  rw [eD_tk] at e
  rw [← e]
  refine LC_f R (tk_bd k hk) fun h => h1 ?_
  rw [wordIn_tk, h]
  rfl

theorem b1_eq : bOneArr = unpack 1755 11 TitsB1 := by
  unfold bOneArr
  rw [wa_eq bW, Nat.eq_of_beq_eq_true bB]

theorem b1_rep :
    Rep 1755 (unpack 1755 11 TitsB1) (wordIn 13 titsT bOneWord) := by
  rw [← b1_eq]
  exact rep_wordArr_titsT (by decide)

theorem b1_facts :
    wordIn 13 titsT bOneWord ≠ 1 ∧ wordIn 13 titsT bOneWord ^ 3 = 1 ∧
      wordIn 13 titsT bOneWord * titsTInv = titsTInv * wordIn 13 titsT bOneWord := by
  have hn : (1755 : Nat) < 2 ^ 32 := by norm_num
  have rB := b1_rep
  have rT : Rep 1755 (unpack 1755 11 TitsT) titsTInv := by
    rw [← TitsInv.t_eq]
    exact titsTInv_rep
  refine ⟨fun e => ?_, ?_, eqP (repP hn rB rT) (repP hn rT rB) bT⟩
  · have h := (eqA_iff rB rep_idA).2 e
    rw [neIdK_sound bNe] at h
    exact absurd h (by decide)
  · rw [pow_three]
    exact eqP (repP hn rB (repP hn rB rB)) id_rep b3

theorem b1_sift : siftA 1755 (rawLevels 1755 titsNArrs (baseArr 1755 titsNBase))
    (baseArr 1755 titsNBase) 0 (unpack 1755 11 TitsB1) = true :=
  siftK_soundR bindsN permN TitsN.hl rfl (hi_of cB) (range_of_canonK cB) kBN

theorem agrSyl : Agrees TitsN.LR TitsN.TR (invTB TitsN.BP TitsT TitsB1) invTest :=
  fun t0 t1 t2 t3 t4 h => by
    rw [invTB_eq bindsN TitsN.head TitsN.hl (NS := 220) (CH := 8) (by norm_num) TitsN.hs
      TitsInv.ndN h TitsInv.cT TitsInv.sTN cB b1_sift, invTest, TitsInv.t_eq, b1_eq]

theorem all5_inv : all5 1755 titsNLevels invTest = true :=
  all5K_soundA bindsN permN TitsN.hl agrSyl TitsSylE.all

theorem inv_of_mem_titsN
    {n : Equiv.Perm (Fin 1755)} (hn : n ∈ titsN) (h2 : n * n = 1)
    (ht : n * titsTInv = titsTInv * n) (hb : n * wordIn 13 titsT bOneWord =
      wordIn 13 titsT bOneWord * n) : n = 1 ∨ n = titsTInv := by
  have rB : Rep 1755 bOneArr (wordIn 13 titsT bOneWord) := by
    rw [b1_eq]
    exact b1_rep
  have hnQ : n ∈ titsQN.originalSubgroup := by rw [titsQN_facts.2.2.1]; exact hn
  have h5 : titsQN.baseCount = 5 := by
    change (finList 1755 titsNBase).length = 5
    simp [finList, titsCentral_check.2.2.1]
  obtain ⟨a, ha, hp⟩ := all5_spec titsN_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.2.1 h5 all5_inv hnQ
  rw [invTest, (commA_iff ha titsTInv_rep).2 ht, (commA_iff ha rB).2 hb,
    (eqA_iff (rep_compA ha ha) rep_idA).2 h2] at hp
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
  rcases hp with h | h
  · exact Or.inl (eq_of_eqA ha rep_idA h)
  · exact Or.inr (eq_of_eqA ha titsTInv_rep h)

theorem facts :
    (sylWords.map (wordIn 13 titsT)).Nodup ∧
      (∀ g ∈ sylWords.map (wordIn 13 titsT), ∀ h ∈ sylWords.map (wordIn 13 titsT),
        g * h ∈ sylWords.map (wordIn 13 titsT)) ∧
      (∀ g ∈ sylWords.map (wordIn 13 titsT), g ^ 3 = 1) ∧
      (∃ g ∈ sylWords.map (wordIn 13 titsT), ∃ h ∈ sylWords.map (wordIn 13 titsT),
        g * h ≠ h * g) ∧
      (∀ w ∈ sylWords, wordIn 13 titsT w ≠ 1 →
        ¬ 5 ∣ Fintype.card {p : Fin 2925 // wordIn 13 titsTStar w p = p} ∧
        ¬ 13 ∣ Fintype.card {p : Fin 2925 // wordIn 13 titsTStar w p = p}) ∧
      wordIn 13 titsT bOneWord ≠ 1 ∧ wordIn 13 titsT bOneWord ^ 3 = 1 ∧
      wordIn 13 titsT bOneWord * titsTInv = titsTInv * wordIn 13 titsT bOneWord ∧
      ∀ n ∈ titsN, n * n = 1 → n * titsTInv = titsTInv * n →
        n * wordIn 13 titsT bOneWord = wordIn 13 titsT bOneWord * n → n = 1 ∨ n = titsTInv :=
  ⟨syl_nodup, fun _ hg _ hh => syl_mul hg hh, fun _ hg => syl_cube hg, syl_noncomm,
    fun _ hw h1 => syl_lines hw h1, b1_facts.1, b1_facts.2.1, b1_facts.2.2,
    fun _ hn h2 ht hb => inv_of_mem_titsN hn h2 ht hb⟩

end CertificateChecks.KernelSporSch.TitsSyl

end
