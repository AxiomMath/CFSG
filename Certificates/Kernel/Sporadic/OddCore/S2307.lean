module

public import Certificates.Kernel.Sporadic.OddCore.S2307K
public import Certificates.Kernel.Sporadic.OddCore.S2307C
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import CFSG.Certificates.Kernel.Spor.EnumBaseSound
public import CFSG.Certificates.Kernel.Spor.EnumBaseLexSound
public import CFSG.Certificates.Kernel.Spor.CardBaseSep
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.HeFixKSnd.Basic
public import CFSG.Certificates.Kernel.SuzCentreKSound
public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.RankThree.Native.PermEnumeration
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2307

open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KS.PEnum CFSG.KS.BaseEq CFSG.KS.EnumBase CFSG.KC.BfsPin CFSG.KS.BfsReplay
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore CFSG.KS.Mathieu

theorem upk_size (P : Nat) : (unpack 1782 11 P).size = 1782 := by simp [unpack]

theorem upk_get {P x : Nat} (hx : x < 1782) : (unpack 1782 11 P)[x]! = pg 11 (mask 11) P x :=
  CFSG.KS.Raw.Orb.unpack_get hx

theorem pp_lt {P x : Nat} (h : PP 1782 11 P) (hx : x < 1782) : pg 11 (mask 11) P x < 1782 :=
  h.2.1 x hx

theorem pgc {P Q x : Nat} (hx : x < 1782) :
    pg 11 (mask 11) (pcomp 1782 11 (mask 11) P Q) x = pg 11 (mask 11) P (pg 11 (mask 11) Q x) :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hx

theorem bp_lt : ∀ p ∈ bp, p < 1782 := by
  intro p hp
  simp only [bp, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem cmpc {P Q : Nat} (hP : canonK 1782 11 (mask 11) (1782 * 11) P = true)
    (hQ : canonK 1782 11 (mask 11) (1782 * 11) Q = true) :
    comp 1782 (unpack 1782 11 P) (unpack 1782 11 Q) = unpack 1782 11 (pcomp 1782 11 (mask 11) P Q) := by
  rw [CFSG.KC.SuzCentreK.comp_eq_compA]
  exact compA_unpack hP hQ

theorem cmp_eq {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    comp 1782 (unpack 1782 11 P) (unpack 1782 11 Q) = unpack 1782 11 (pcomp 1782 11 (mask 11) P Q) :=
  cmpc hP.1 hQ.1

theorem upk_inj {p q : Nat} (hp : canonK 1782 11 (mask 11) (1782 * 11) p = true)
    (hq : canonK 1782 11 (mask 11) (1782 * 11) q = true)
    (h : unpack 1782 11 p = unpack 1782 11 q) : p = q := by
  obtain ⟨-, hw, hp1, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq1, -⟩ := CFSG.KS.PF.canon_facts hq
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp1 hq1 fun i hi => ?_
  rw [← CFSG.KS.Raw.Orb.unpack_get hi, ← CFSG.KS.Raw.Orb.unpack_get hi, h]

theorem beq_eq' {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    (unpack 1782 11 P == unpack 1782 11 Q) = Nat.beq P Q :=
  CFSG.KC.HeFixKSnd.beq_unpack_PP hP hQ

theorem idTab_eq : idTab 1782 = unpack 1782 11 (pidn 1782 11) := by
  rw [CFSG.KC.SuzCentreK.idTab_eq_idA]
  exact idA_eq szk

theorem pid_PP : PP 1782 11 (pidn 1782 11) := PP.id szk

theorem g_PP {g : Nat} (hg : g < 11) : PP 1782 11 (SSE.G g) :=
  PP_of_permOK szk (allN_spec pG g hg)

theorem g_get : invSylowArrs.size = 11 ∧ ∀ g < 11, invSylowArrs[g]! = unpack 1782 11 (SSE.G g) := by
  have e : invSylowArrs = Array.ofFn (n := 11) fun j => invFusionRun j.val := rfl
  refine ⟨by rw [e, Array.size_ofFn], fun g hg => ?_⟩
  rw [e, getElem!_pos _ g (by simpa using hg), Array.getElem_ofFn, fusionRun_eq (by omega),
    ← Nat.eq_of_beq_eq_true (allN_spec gb g hg)]

theorem gi_eq {g : Nat} (hg : g < 11) : SSE.GI g = pinvS 1782 11 (mask 11) (SSE.G g) :=
  Nat.eq_of_beq_eq_true (allN_spec gI g hg)

theorem gi_PP {g : Nat} (hg : g < 11) : PP 1782 11 (SSE.GI g) := by
  rw [gi_eq hg]
  exact (g_PP hg).inv

theorem gi_get {g : Nat} (hg : g < 11) : sylowInvs[g]! = unpack 1782 11 (SSE.GI g) := by
  unfold sylowInvs
  rw [getElem!_pos _ g (by rw [Array.size_map, g_get.1]; exact hg), Array.getElem_map,
    ← getElem!_pos invSylowArrs g (by rw [g_get.1]; exact hg), g_get.2 g hg,
    CFSG.KC.HeFixKSnd.invTab_unpack_PP (g_PP hg), gi_eq hg]

theorem invs_size : sylowInvs.size = 11 := by
  unfold sylowInvs
  rw [Array.size_map, g_get.1]

@[expose] noncomputable def ET (i : Nat) : Tab := unpack 1782 11 (SSE.T i)

@[expose] noncomputable def EA : Array Tab := Array.ofFn (n := 16384) fun i => ET i.val

theorem EA_size : EA.size = 16384 := by simp [EA]

theorem EA_get {k : Nat} (hk : k < 16384) : EA[k]! = ET k := by
  unfold EA
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem rec_get {k : Nat} (hk : k < 16384) :
    recK 1782 11 (mask 11) 11 SSE.G SSE.T SSE.PL k = true :=
  sliceK_spec (S := 256) (by norm_num) (by norm_num) (fun s hs => rsK.all s hs) k hk

theorem ls_get {k : Nat} (hk : k < 16384) :
    leftK 11 (mask 11) bp 11 16384 SSE.G SSE.T SSE.POS k = true ∧
      lexPosK 11 16384 SSE.PL SSE.POS k = true := by
  have h := sliceK_spec (S := 256) (by norm_num) (by norm_num) (fun s hs => lsK.all s hs) k hk
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem T_zero : SSE.T 0 = pidn 1782 11 := (recK_spec (rec_get (by norm_num))).1 rfl

theorem T_PP : ∀ k < 16384, PP 1782 11 (SSE.T k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have r := recK_spec (rec_get hk)
    by_cases k0 : k = 0
    · subst k0
      rw [T_zero]
      exact pid_PP
    · obtain ⟨h1, h2, h3⟩ := r.2 k0
      rw [h3]
      exact (g_PP h2).mul (ih _ h1 (by omega))

theorem ET_zero : ET 0 = idTab 1782 := by rw [ET, T_zero, idTab_eq]

theorem ET_rec {k : Nat} (hk : k < 16384) (k0 : k ≠ 0) :
    parOf SSE.PL k < k ∧ labOf SSE.PL k < 11 ∧
      ET k = leftStep 1782 invSylowArrs (labOf SSE.PL k) (ET (parOf SSE.PL k)) := by
  obtain ⟨h1, h2, h3⟩ := (recK_spec (rec_get hk)).2 k0
  refine ⟨h1, h2, ?_⟩
  unfold leftStep ET
  rw [g_get.2 _ h2, cmp_eq (g_PP h2) (T_PP _ (by omega)), ← h3]

@[expose] noncomputable def H : Subgroup (Equiv.Perm (Fin 1782)) :=
  CFSG.Sporadic.HNOddCore.arrGen 1782 invSylowArrs

@[expose] noncomputable def pm (P : Nat) : Equiv.Perm (Fin 1782) := permOfArr 1782 (unpack 1782 11 P)

theorem rep_pm {P : Nat} (h : PP 1782 11 P) : Rep 1782 (unpack 1782 11 P) (pm P) :=
  rep_of_validA (validA_unpack (CFSG.KS.PinvS.permOK_pinvS h.1 h.2))

theorem pm_mul {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    pm (pcomp 1782 11 (mask 11) P Q) = pm P * pm Q := by
  have h := rep_compA (rep_pm hP) (rep_pm hQ)
  rw [compA_PP hP hQ] at h
  exact (rep_pm (hP.mul hQ)).unique h

theorem pm_id : pm (pidn 1782 11) = 1 := by
  have h := rep_pm pid_PP
  rw [← idA_eq szk] at h
  exact h.unique rep_idA

theorem pm_inv {P : Nat} (hP : PP 1782 11 P) : pm (pinvS 1782 11 (mask 11) P) = (pm P)⁻¹ := by
  have h := rep_compA (rep_pm hP.inv) (rep_pm hP)
  have e : compA 1782 (unpack 1782 11 (pinvS 1782 11 (mask 11) P)) (unpack 1782 11 P) =
      idA 1782 := CFSG.KC.HeFixKSnd.comp_inv_left_PP hP
  rw [e] at h
  exact eq_inv_of_mul_eq_one_left (rep_idA.unique h).symm

theorem pm_get {P : Nat} (hP : PP 1782 11 P) (x : Fin 1782) :
    (pm P x : Nat) = pg 11 (mask 11) P x := by
  rw [← (rep_pm hP).apply x.2, upk_get x.2]

theorem pm_ext {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) (h : pm P = pm Q) : P = Q := by
  obtain ⟨-, hw, hp1, -⟩ := CFSG.KS.PF.canon_facts hP.1
  obtain ⟨-, -, hq1, -⟩ := CFSG.KS.PF.canon_facts hQ.1
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp1 hq1 fun i hi => ?_
  rw [← pm_get hP ⟨i, hi⟩, ← pm_get hQ ⟨i, hi⟩, h]

@[expose] def MemP (P : Nat) : Prop := PP 1782 11 P ∧ pm P ∈ H

theorem mem_mul {P Q : Nat} (hP : MemP P) (hQ : MemP Q) : MemP (pcomp 1782 11 (mask 11) P Q) :=
  ⟨hP.1.mul hQ.1, by rw [pm_mul hP.1 hQ.1]; exact H.mul_mem hP.2 hQ.2⟩

theorem mem_id : MemP (pidn 1782 11) := ⟨pid_PP, by rw [pm_id]; exact H.one_mem⟩

theorem mem_g {g : Nat} (hg : g < 11) : MemP (SSE.G g) := by
  refine ⟨g_PP hg, Subgroup.subset_closure ⟨g, by rw [g_get.1]; exact hg, ?_⟩⟩
  rw [g_get.2 g hg]
  rfl

theorem mem_gi {g : Nat} (hg : g < 11) : MemP (SSE.GI g) := by
  rw [gi_eq hg]
  exact ⟨(g_PP hg).inv, by rw [pm_inv (g_PP hg)]; exact H.inv_mem (mem_g hg).2⟩

theorem mem_T : ∀ k < 16384, MemP (SSE.T k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have r := recK_spec (rec_get hk)
    by_cases k0 : k = 0
    · subst k0
      rw [T_zero]
      exact mem_id
    · obtain ⟨h1, h2, h3⟩ := r.2 k0
      rw [h3]
      exact mem_mul (mem_g h2) (ih _ h1 (by omega))

@[expose] noncomputable def WW : Array (List Int) := (List.replicate 11 [] ++ SSD).toArray

@[expose] def bpF : List (Fin 1782) := [0, 1]

theorem bpF_nodup : bpF.Nodup := by decide

theorem base_of {n w nb BP : Nat} {base : List (Fin n)} (hs : (base.map Fin.val).toArray.size = nb)
    (h : allN nb (fun t => Nat.beq (pg w (mask w) BP t) ((base.map Fin.val).toArray[t]!)) = true) :
    (base.map Fin.val).toArray.size = nb ∧
      ∀ t < nb, (base.map Fin.val).toArray[t]! = pg w (mask w) BP t :=
  ⟨hs, fun t ht => (Nat.eq_of_beq_eq_true (allN_spec h t ht)).symm⟩

theorem ch : CFSG.Sporadic.HNOddCore.chainCheck 1782 invSylowArrs WW bpF [128, 128] = true :=
  chainCheck_of ⟨g_get.1, fun j hj => by
      rw [g_get.2 j hj, Nat.eq_of_beq_eq_true (allN_spec hpc j hj)]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num)
    (base_of (by decide +kernel) bPC) SSC.head SSC.hl (by decide +kernel) SSC.hs pPC
    (by decide +kernel)

theorem H_card : Nat.card H = 16384 := by
  unfold H
  rw [CFSG.Sporadic.HNOddCore.card_arrGen_of_chainCheck (by norm_num) bpF_nodup ch]
  rfl

theorem keyK_congr {ps : List Nat} {t u : Nat}
    (h : ∀ p ∈ ps, pg 11 (mask 11) t p = pg 11 (mask 11) u p) :
    keyK 1782 11 ps t = keyK 1782 11 ps u := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change Nat.add (pg 11 (mask 11) t p) (Nat.mul 1782 (keyK 1782 11 ps t)) =
      Nat.add (pg 11 (mask 11) u p) (Nat.mul 1782 (keyK 1782 11 ps u))
    rw [h p List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem p hq)]

theorem T_inj {i j : Nat} (hi : i < 16384) (hj : j < 16384)
    (h : ∀ p ∈ bp, pg 11 (mask 11) (SSE.T i) p = pg 11 (mask 11) (SSE.T j) p) : i = j :=
  keysSK_spec keys i hi j hj (keyK_congr h)

theorem T_inj' {i j : Nat} (hi : i < 16384) (hj : j < 16384) (h : SSE.T i = SSE.T j) : i = j :=
  T_inj hi hj fun p _ => by rw [h]

theorem bpF_mem : ∀ b ∈ bpF, (b : Nat) ∈ bp := by
  intro b hb
  simp only [bpF, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;> simp [bp]

theorem bp_memF : ∀ p ∈ bp, ∃ b ∈ bpF, (b : Nat) = p := by
  intro p hp
  simp only [bp, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨0, by simp [bpF], rfl⟩
  · exact ⟨1, by simp [bpF], rfl⟩

theorem sepP {P Q : Nat} (hP : MemP P) (hQ : MemP Q)
    (h : ∀ p ∈ bp, pg 11 (mask 11) P p = pg 11 (mask 11) Q p) : P = Q := by
  refine pm_ext hP.1 hQ.1 (CFSG.KS.CardSep.eq_of_base H_card (ε := fun k => pm (SSE.T k))
    (fun k hk => (mem_T k hk).2) (B := bpF) (fun i hi j hj hij => T_inj hi hj fun p hp => ?_)
    hP.2 hQ.2 fun b hb => Fin.ext ?_)
  · obtain ⟨b, hb, rfl⟩ := bp_memF p hp
    rw [← pm_get (mem_T i hi).1, ← pm_get (mem_T j hj).1, hij b hb]
  · rw [pm_get hP.1, pm_get hQ.1]
    exact h b (bpF_mem b hb)

theorem left_eq {g k : Nat} (hg : g < 11) (hk : k < 16384) :
    r32 SSE.POS (k * 11 + g) < 16384 ∧
      pcomp 1782 11 (mask 11) (SSE.G g) (SSE.T k) = SSE.T (r32 SSE.POS (k * 11 + g)) := by
  have hl := leftK_spec (ls_get hk).1 g hg
  refine ⟨hl.1, sepP (mem_mul (mem_g hg) (mem_T k hk)) (mem_T _ hl.1) fun p hp => ?_⟩
  rw [pgc (bp_lt p hp)]
  exact hl.2 p hp

theorem conj_eq {g x y : Nat} (hg : g < 11) (hx : x < 16384) (hy : y < 16384)
    (h : ∀ p ∈ bp, pg 11 (mask 11) (SSE.G g) (pg 11 (mask 11) (SSE.T x)
      (pg 11 (mask 11) (SSE.GI g) p)) = pg 11 (mask 11) (SSE.T y) p) :
    pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) (SSE.G g) (SSE.T x)) (SSE.GI g) = SSE.T y := by
  refine sepP (mem_mul (mem_mul (mem_g hg) (mem_T x hx)) (mem_gi hg)) (mem_T y hy) fun p hp => ?_
  have hp' := bp_lt p hp
  rw [pgc hp', pgc (pp_lt (gi_PP hg) hp')]
  exact h p hp

theorem sq_iff {k : Nat} (hk : k < 16384) :
    pcomp 1782 11 (mask 11) (SSE.T k) (SSE.T k) = pidn 1782 11 ↔
      sqFixK 11 (mask 11) bp (SSE.T k) = true := by
  rw [sqFixK_iff]
  constructor
  · intro h p hp
    rw [← pgc (bp_lt p hp), h, CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) (bp_lt p hp)]
  · intro h
    refine sepP (mem_mul (mem_T k hk) (mem_T k hk)) mem_id fun p hp => ?_
    rw [pgc (bp_lt p hp), CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) (bp_lt p hp)]
    exact h p hp

theorem T_eq_id {k : Nat} (hk : k < 16384) : SSE.T k = pidn 1782 11 ↔ k = 0 := by
  constructor
  · intro h
    exact T_inj' hk (by norm_num) (by rw [h, T_zero])
  · rintro rfl
    exact T_zero

theorem isInv_ET {k : Nat} (hk : k < 16384) :
    isInvTab (ET k) = (sqFixK 11 (mask 11) bp (SSE.T k) && !(Nat.beq k 0)) := by
  unfold isInvTab ET
  rw [cmp_eq (T_PP k hk) (T_PP k hk), idTab_eq, beq_eq' ((T_PP k hk).mul (T_PP k hk)) pid_PP,
    beq_eq' (T_PP k hk) pid_PP]
  congr 1
  · rw [Bool.eq_iff_iff, Nat.beq_eq, ← sq_iff hk]
  · congr 1
    rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.beq_eq, T_eq_id hk]

theorem lexK_iff {a b c d : Nat} : lexLtK a b c d = true ↔ CFSG.KS.BfsReplay.LexLt a b c d := by
  unfold lexLtK CFSG.KS.BfsReplay.LexLt
  rw [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.blt_dec,
    CFSG.KS.Raw.Orb.beq_dec, CFSG.KS.Raw.Orb.blt_dec]
  by_cases h : a < c
  · simp [h]
  · simp [h]

theorem not_lex_of {a b c d : Nat} (h : lexLtK a b c d = false) :
    ¬ CFSG.KS.BfsReplay.LexLt a b c d := by
  intro hl
  have := lexK_iff.2 hl
  rw [h] at this
  exact absurd this Bool.false_ne_true

theorem pl_zero : parOf SSE.PL 0 = 0 ∧ labOf SSE.PL 0 = 0 := by
  unfold parOf labOf
  rw [Nat.eq_of_beq_eq_true pl0]
  exact ⟨rfl, rfl⟩

theorem step_eq {j h : Nat} (hj : j < 11) (hh : h < 16384) :
    leftStep 1782 invSylowArrs j (ET h) = ET (r32 SSE.POS (h * 11 + j)) := by
  unfold leftStep ET
  rw [g_get.2 j hj, cmp_eq (g_PP hj) (T_PP h hh), (left_eq hj hh).2]

theorem replayS : Replay (leftStep 1782 invSylowArrs) invSylowArrs.size (idTab 1782) 16384 ET
    (parOf SSE.PL) (labOf SSE.PL) (fun h j => r32 SSE.POS (h * 11 + j)) := by
  rw [g_get.1]
  refine ⟨by norm_num, ET_zero, pl_zero.1, pl_zero.2, fun a ha b hb e => ?_, fun i h0 hi => ?_,
    fun i h0 hi => ?_, fun h hh j hj => ?_⟩
  · exact T_inj' ha hb (upk_inj (T_PP a ha).1 (T_PP b hb).1 e)
  · obtain ⟨a1, a2, a3⟩ := ET_rec hi (by omega)
    exact ⟨a1, a2, a3⟩
  · exact lexK_iff.1 ((lexPosK_spec (ls_get (by omega)).2).1 h0 hi)
  · refine ⟨(left_eq hj hh).1, step_eq hj hh, ?_⟩
    rcases (lexPosK_spec (ls_get hh).2).2 j hj with e | e
    · exact Or.inl e
    · exact Or.inr (not_lex_of e)

@[expose] noncomputable def ER : Enum :=
  ⟨EA, Array.ofFn (n := 16384) fun i => parOf SSE.PL i.val,
    Array.ofFn (n := 16384) fun i => labOf SSE.PL i.val⟩

theorem sylowEnum_eq : sylowEnum = ER ∧ enumOK 1782 invSylowArrs ER = true := by
  have := enumBFS_replay replayS le_rfl
  exact this

theorem ER_tabs : ER.tabs = EA := by
  unfold ER
  rfl

@[expose] noncomputable def O (c : Nat) : Nat := r32 SSF.O c
@[expose] noncomputable def cnt (c : Nat) : Nat := O (c + 1) - O c
@[expose] noncomputable def Lr (c j : Nat) : Nat := r32 SSF.L (O c + j)
@[expose] noncomputable def Pr (c j : Nat) : Nat := r32 SSF.P (O c + j)
@[expose] noncomputable def Gr (c j : Nat) : Nat := r32 SSF.G (O c + j)
@[expose] noncomputable def Qr (c j g : Nat) : Nat := r32 SSF.Q ((O c + j) * 11 + g)

theorem cl_spec {c : Nat} (hc : c < 22) :
    0 < cnt c ∧ cnt c ≤ 16384 ∧ Pr c 0 = 0 ∧ Gr c 0 = 0 ∧
      sqFixK 11 (mask 11) bp (SSE.T (Lr c 0)) = true ∧
      ∀ j < cnt c, classPtK 11 (mask 11) bp 11 16384 SSE.G SSE.GI SSE.T (r32 SSF.L) (r32 SSF.P)
        (r32 SSF.G) (r32 SSF.Q) (r32 SSF.MK) (r32 SSF.PX) c (O c) (cnt c) j = true := by
  have h := classK_spec (clK.all c hc)
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h2, h3, h4, h5, h6, h7⟩

theorem Lr_lt {c j : Nat} (hc : c < 22) (hj : j < cnt c) : Lr c j < 16384 :=
  (classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).1

theorem Lr_mk {c j : Nat} (hc : c < 22) (hj : j < cnt c) : r32 SSF.MK (Lr c j) = c :=
  (classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).2.1

theorem Lr_px {c j : Nat} (hc : c < 22) (hj : j < cnt c) : r32 SSF.PX (Lr c j) = j :=
  (classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).2.2.1

theorem Lr_inj {c j c' j' : Nat} (hc : c < 22) (hj : j < cnt c) (hc' : c' < 22)
    (hj' : j' < cnt c') (h : Lr c j = Lr c' j') : c = c' ∧ j = j' := by
  refine ⟨?_, ?_⟩
  · rw [← Lr_mk hc hj, ← Lr_mk hc' hj', h]
  · rw [← Lr_px hc hj, ← Lr_px hc' hj', h]

theorem ET_inj {a b : Nat} (ha : a < 16384) (hb : b < 16384) (h : ET a = ET b) : a = b :=
  T_inj' ha hb (upk_inj (T_PP a ha).1 (T_PP b hb).1 h)

theorem nif_eq (c : Bool) (a b : Nat) : nIf(c, a, b) = if c = true then a else b := by
  cases c <;> rfl

theorem cnt_eq {c : Nat} (hc : c < 22) :
    cnt c = if c < 21 then invFusionSizes.getD c 0 else 1 := by
  have h := Nat.eq_of_beq_eq_true (allN_spec sizes c hc)
  unfold cnt O
  change Nat.sub (r32 SSF.O (Nat.succ c)) (r32 SSF.O c) = _
  rw [h, nif_eq, nget_eq]
  by_cases h21 : c < 21
  · rw [if_pos (Nat.blt_eq.mpr h21), if_pos h21]
  · rw [if_neg (fun e => h21 (Nat.blt_eq.mp e)), if_neg h21]

theorem cnt_fus {r : Nat} (hr : r < 21) : cnt r = invFusionSizes.getD r 0 := by
  rw [cnt_eq (by omega), if_pos hr]

theorem cnt_le {c : Nat} (hc : c < 22) : cnt c ≤ 128 := by
  rw [cnt_eq hc]
  split
  · next h => interval_cases c <;> decide
  · omega

theorem conjStep_eq {g x : Nat} (hg : g < 11) (hx : x < 16384) :
    conjStep 1782 invSylowArrs sylowInvs g (ET x) =
      unpack 1782 11 (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) (SSE.G g) (SSE.T x))
        (SSE.GI g)) := by
  unfold conjStep conjTab ET
  rw [g_get.2 g hg, gi_get hg, cmp_eq (g_PP hg) (T_PP x hx),
    cmp_eq ((g_PP hg).mul (T_PP x hx)) (gi_PP hg)]

theorem tree_conj {c j : Nat} (hc : c < 22) (hj : j < cnt c) (j0 : j ≠ 0) :
    Pr c j < j ∧ Gr c j < 11 ∧
      ET (Lr c j) = conjStep 1782 invSylowArrs sylowInvs (Gr c j) (ET (Lr c (Pr c j))) := by
  obtain ⟨h1, h2, h3⟩ := ((classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).2.2.2.1 j0)
  have h1' : Pr c j < j := h1
  have h2' : Gr c j < 11 := h2
  refine ⟨h1', h2', ?_⟩
  rw [conjStep_eq h2' (Lr_lt hc (by omega))]
  exact (congrArg (unpack 1782 11) (conj_eq h2' (Lr_lt hc (by omega)) (Lr_lt hc hj) h3.1)).symm

theorem close_conj {c j g : Nat} (hc : c < 22) (hj : j < cnt c) (hg : g < 11) :
    Qr c j g < cnt c ∧
      conjStep 1782 invSylowArrs sylowInvs g (ET (Lr c j)) = ET (Lr c (Qr c j g)) ∧
      (Qr c j g = 0 ∨ ¬ CFSG.KS.BfsReplay.LexLt j g (Pr c (Qr c j g)) (Gr c (Qr c j g))) := by
  obtain ⟨h1, h2, h3⟩ := (classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).2.2.2.2 g hg
  have h1' : Qr c j g < cnt c := h1
  refine ⟨h1', ?_, ?_⟩
  · rw [conjStep_eq hg (Lr_lt hc hj)]
    exact congrArg (unpack 1782 11) (conj_eq hg (Lr_lt hc hj) (Lr_lt hc h1') h2)
  · rcases h3 with e | e
    · exact Or.inl e
    · exact Or.inr (not_lex_of e)

theorem lt53a {r : Nat} (hr : r < 21) : Nat.add 11 (Nat.mul 2 r) < 53 := by
  change 11 + 2 * r < 53
  omega

theorem lt53b {r : Nat} (hr : r < 21) : Nat.add 12 (Nat.mul 2 r) < 53 := by
  change 12 + 2 * r < 53
  omega

theorem rep_fus {r : Nat} (hr : r < 21) :
    invFusionRepArr r = unpack 1782 11 (SuzFusT.F (Nat.add 11 (Nat.mul 2 r))) := by
  unfold invFusionRepArr
  exact fusionRun_eq (lt53a hr)

theorem conj_fus {r : Nat} (hr : r < 21) :
    invFusionConjArr r = unpack 1782 11 (SuzFusT.F (Nat.add 12 (Nat.mul 2 r))) := by
  unfold invFusionConjArr
  exact fusionRun_eq (lt53b hr)

theorem rep_eq {r : Nat} (hr : r < 21) : ET (Lr r 0) = invFusionRepArr r := by
  have e : SSE.T (Lr r 0) = SuzFusT.F (Nat.add 11 (Nat.mul 2 r)) := by
    have := Nat.eq_of_beq_eq_true (allN_spec reps r hr)
    unfold Lr O
    rw [Nat.add_zero]
    exact this
  rw [rep_fus hr, ET, e]

theorem replayF {r : Nat} (hr : r < 21) :
    Replay (conjStep 1782 invSylowArrs sylowInvs) 11 (invFusionRepArr r) (cnt r)
      (fun j => ET (Lr r j)) (Pr r) (Gr r) (Qr r) := by
  have hc : r < 22 := by omega
  obtain ⟨h1, -, h3, h4, -, h6⟩ := cl_spec hc
  refine ⟨h1, rep_eq hr, h3, h4, fun a ha b hb e => ?_, fun i h0 hi => tree_conj hc hi (by omega),
    fun i h0 hi => ?_, fun h hh j hj => close_conj hc hh hj⟩
  · exact (Lr_inj hc ha hc hb (ET_inj (Lr_lt hc ha) (Lr_lt hc hb) e)).2
  · obtain ⟨-, -, -, a4⟩ := ((classPtK_spec (h6 i (by omega))).2.2.2.1 (by omega))
    exact lexK_iff.1 (a4 hi)

@[expose] noncomputable def FR (r : Nat) : Enum :=
  ⟨Array.ofFn (n := cnt r) fun j => ET (Lr r j.val), Array.ofFn (n := cnt r) fun j => Pr r j.val,
    Array.ofFn (n := cnt r) fun j => Gr r j.val⟩

theorem fusionEnum_eq {r : Nat} (hr : r < 21) :
    fusionEnum r = FR r ∧
      treeOK (conjStep 1782 invSylowArrs sylowInvs) invSylowArrs.size (invFusionRepArr r) (FR r) =
        true := by
  have := bfs_replay (cap := 1000) (replayF hr) (by have := cnt_le (by omega : r < 22); omega)
  unfold fusionEnum orbitBFS
  rw [g_get.1]
  exact this

@[expose] noncomputable def FA : Array Enum := Array.ofFn (n := 21) fun r => FR r.val

theorem FA_size : FA.size = 21 := by
  unfold FA
  rw [Array.size_ofFn]

theorem FA_get {r : Nat} (hr : r < 21) : FA[r]! = FR r := by
  unfold FA
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]

theorem fusionEnums_eq : fusionEnums = FA := by
  apply Array.ext
  · simp [fusionEnums, FA]
  · intro r h1 h2
    have hr : r < 21 := by simpa [FA] using h2
    rw [← getElem!_pos _ r h1, ← getElem!_pos FA r h2, FA_get hr]
    unfold fusionEnums
    rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
    exact (fusionEnum_eq hr).1

theorem FR_size (r : Nat) : (FR r).tabs.size = cnt r := by simp [FR]

theorem FR_get {r j : Nat} (hj : j < cnt r) : (FR r).tabs[j]! = ET (Lr r j) := by
  unfold FR
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem fus_PP {k : Nat} (hk : k < 53) : PP 1782 11 (SuzFusT.F k) :=
  @PP_of_permOK' 1782 11 (SuzFusT.F k) (SuzFusI k) szk (allN_spec fus_perms k hk)

theorem mk_zero : r32 SSF.MK 0 = 21 := by
  have e : Lr 21 0 = 0 := by
    unfold Lr O
    rw [Nat.add_zero]
    exact Nat.eq_of_beq_eq_true rep21
  have := Lr_mk (c := 21) (j := 0) (by norm_num) (by rw [cnt_eq (by norm_num)]; norm_num)
  rwa [e] at this

theorem Lr_ne_zero {r j : Nat} (hr : r < 21) (hj : j < cnt r) : Lr r j ≠ 0 := by
  intro e
  have := Lr_mk (by omega : r < 22) hj
  rw [e, mk_zero] at this
  omega

theorem permOK_unp {P : Nat} (hP : PP 1782 11 P) :
    CFSG.Sporadic.SuzOddCore.permOK 1782 (unpack 1782 11 P) = true := by
  unfold CFSG.Sporadic.SuzOddCore.permOK
  rw [Bool.and_eq_true, beq_iff_eq]
  exact ⟨upk_size P, validA_unpack (CFSG.KS.PinvS.permOK_pinvS hP.1 hP.2)⟩

theorem inT_unp {P : Nat} (hP : PP 1782 11 P) : inT (unpack 1782 11 P) = inTK P := by
  unfold inT inTK
  rw [inM_eq rfl hP.1, Suz2306.vArr_eq, compA_unpack canonV hP.1,
    inM_eq rfl (canonK_pcomp canonV hP.1), bIf_eq]
  cases h : msift P <;> simp

theorem gens_ok : allBelow 11 (fun k => CFSG.Sporadic.SuzOddCore.permOK 1782 invSylowArrs[k]! &&
    inT invSylowArrs[k]!) = true := by
  refine allBelow_iff.2 fun k hk => ?_
  rw [g_get.2 k hk, Bool.and_eq_true, inT_unp (g_PP hk), Nat.eq_of_beq_eq_true (allN_spec gb k hk)]
  exact ⟨permOK_unp (fus_PP (by omega)), allN_spec inG k hk⟩

theorem EA_toList : EA.toList = (List.range 16384).map ET := by
  apply List.ext_getElem
  · rw [Array.length_toList, EA_size, List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < 16384 := by rwa [Array.length_toList, EA_size] at h1
    rw [Array.getElem_toList, List.getElem_map, List.getElem_range,
      ← getElem!_pos EA i (by rw [EA_size]; exact hi), EA_get hi]

theorem inv_count : (EA.toList.filter isInvTab).length = 911 := by
  rw [EA_toList, ← List.countP_eq_length_filter, List.countP_map]
  have e : (List.range 16384).countP (isInvTab ∘ ET) =
      (List.range 16384).countP (fun k => bIf(Nat.beq k (nat_lit 0), false,
        sqFixK 11 (mask 11) bp (SSE.T k))) := by
    refine List.countP_congr fun k hk => ?_
    have hk' := List.mem_range.1 hk
    rw [Function.comp_apply, isInv_ET hk', bIf_eq]
    by_cases k0 : k = 0
    · subst k0
      simp
    · have e0 : Nat.beq k 0 = false := by rw [beq_eq]; simpa using k0
      rw [e0]
      simp
  rw [e, ← cntN_eq]
  exact Nat.eq_of_beq_eq_true sqCnt

theorem invs_ok : invsOK 1782 invSylowArrs sylowInvs = true := by
  unfold invsOK
  rw [Bool.and_eq_true, beq_iff_eq, invs_size, g_get.1, allBelow_iff]
  refine ⟨rfl, fun k hk => ?_⟩
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, gi_get hk, g_get.2 k hk, gi_eq hk]
  exact ⟨upk_size _, CFSG.KC.HeFixKSnd.comp_inv_left_PP (g_PP hk)⟩

theorem rec_ok {r : Nat} (hr : r < 21) : fusionRecOK r (FR r) ER (indexOf EA) = true := by
  have hc : r < 22 := by omega
  have hfc : fusionCase r = nget invFusionCases r := by
    unfold fusionCase
    rw [nget_eq]
  have hcase : fusionCase r < 4 := by
    rw [hfc]
    exact Nat.blt_eq.mp (allN_spec cases_lt r hr)
  have hC := fus_PP (lt53b hr)
  obtain ⟨htA, htC, -⟩ := rep_facts hcase
  unfold fusionRecOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hcase⟩, ?_⟩, ?_⟩
  · unfold orbitOK
    rw [Bool.and_eq_true]
    exact ⟨invs_ok, (fusionEnum_eq hr).2⟩
  · rw [FR_size, cnt_fus hr]
  · rw [rep_fus hr]
    exact permOK_unp (fus_PP (lt53a hr))
  · rw [← rep_eq hr, isInv_ET (Lr_lt hc (cl_spec hc).1), (cl_spec hc).2.2.2.2.1, Bool.true_and,
      Bool.not_eq_true', beq_eq, decide_eq_false_iff_not]
    exact Lr_ne_zero hr (cl_spec hc).1
  · rw [ER_tabs, found_indexOf_iff]
    exact ⟨Lr r 0, by rw [EA_size]; exact Lr_lt hc (cl_spec hc).1,
      by rw [EA_get (Lr_lt hc (cl_spec hc).1), rep_eq hr]⟩
  · rw [conj_fus hr]
    exact permOK_unp hC
  · rw [conj_fus hr, invCand_PP hC, upk_size]
  · rw [conj_fus hr, inT_unp hC]
    exact allN_spec inC r hr
  · rw [htA, upk_size]
  · unfold conjTab
    rw [conj_fus hr, invCand_PP hC, htA, cmpc hC.1 htC, cmpc (canonK_pcomp hC.1 htC) hC.inv.1,
      rep_fus hr, hfc, Nat.eq_of_beq_eq_true (allN_spec conjs r hr)]

theorem notin_ok {r r' : Nat} (hr : r < 21) (hr' : r' < 21) :
    (r == r' || notInOK (FR r).tabs (invFusionRepArr r')) = true := by
  by_cases e : r = r'
  · simp [e]
  · rw [Bool.or_eq_true]
    right
    unfold notInOK
    rw [allBelow_iff]
    intro k hk
    rw [FR_size] at hk
    rw [FR_get hk, ← rep_eq hr', Bool.not_eq_true', ET, ET,
      beq_eq' (T_PP _ (Lr_lt (by omega) hk)) (T_PP _ (Lr_lt (by omega) (cl_spec (by omega)).1))]
    cases h : Nat.beq (SSE.T (Lr r k)) (SSE.T (Lr r' 0))
    · rfl
    · exfalso
      have h1 := T_inj' (Lr_lt (by omega) hk) (Lr_lt (by omega) (cl_spec (by omega)).1)
        (Nat.eq_of_beq_eq_true h)
      exact e (Lr_inj (by omega) hk (by omega) (cl_spec (by omega)).1 h1).1

theorem cover_ok : CFSG.PSL3Four.Native.coverOK 1782 EA (FA.map Enum.tabs) = true := by
  unfold CFSG.PSL3Four.Native.coverOK
  simp only []
  rw [allBelow_iff]
  intro k hk
  rw [EA_size] at hk
  rw [EA_get hk, Bool.or_eq_true, Bool.or_eq_true]
  by_cases k0 : k = 0
  · subst k0
    left
    left
    rw [ET_zero]
    exact beq_self_eq_true _
  by_cases hs : sqFixK 11 (mask 11) bp (SSE.T k) = true
  · right
    obtain ⟨a1, a2, a3⟩ := coverK_spec (sliceK_spec (S := 16) (by norm_num) (by norm_num)
      (fun s hs => cvK.all s hs) k hk) hs
    have hmk : r32 SSF.MK k < 21 := by
      by_contra hn
      have e21 : r32 SSF.MK k = 21 := by omega
      have hc1 : cnt 21 = 1 := by rw [cnt_eq (by norm_num)]; norm_num
      have hp : r32 SSF.PX k = 0 := by
        have : r32 SSF.PX k < cnt 21 := by rw [e21] at a2; exact a2
        omega
      have e : Lr 21 0 = k := by
        have := a3
        rw [e21, hp] at this
        exact this
      have e0 : Lr 21 0 = 0 := by
        unfold Lr O
        rw [Nat.add_zero]
        exact Nat.eq_of_beq_eq_true rep21
      omega
    unfold anyBelow
    rw [List.any_eq_true]
    have hm' : r32 SSF.MK k < FA.size := by rw [FA_size]; exact hmk
    have e1 : (FA.map Enum.tabs)[r32 SSF.MK k]! = (FR (r32 SSF.MK k)).tabs := by
      rw [getElem!_pos _ _ (by rw [Array.size_map]; exact hm'), Array.getElem_map,
        ← getElem!_pos FA _ hm', FA_get hmk]
    have e2 : ((FA.map Enum.tabs).map indexOf)[r32 SSF.MK k]! = indexOf (FR (r32 SSF.MK k)).tabs := by
      rw [getElem!_pos _ _ (by rw [Array.size_map, Array.size_map]; exact hm'), Array.getElem_map,
        ← getElem!_pos (FA.map Enum.tabs) _ (by rw [Array.size_map]; exact hm'), e1]
    refine ⟨r32 SSF.MK k, List.mem_range.2 (by rw [Array.size_map]; exact hm'), ?_⟩
    rw [e1, e2, found_indexOf_iff]
    refine ⟨r32 SSF.PX k, by rw [FR_size]; exact a2, ?_⟩
    rw [FR_get a2]
    unfold Lr O
    rw [a3]
  · left
    right
    unfold ET
    rw [cmp_eq (T_PP k hk) (T_PP k hk), idTab_eq, beq_eq' ((T_PP k hk).mul (T_PP k hk)) pid_PP,
      Bool.not_eq_true', Bool.eq_false_iff]
    intro h
    exact hs ((sq_iff hk).1 (Nat.eq_of_beq_eq_true h))

theorem FR_toList (r : Nat) : (FR r).tabs.toList = (List.range (cnt r)).map fun j => ET (Lr r j) := by
  apply List.ext_getElem
  · rw [Array.length_toList, FR_size, List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < cnt r := by rwa [Array.length_toList, FR_size] at h1
    rw [Array.getElem_toList, List.getElem_map, List.getElem_range,
      ← getElem!_pos (FR r).tabs i (by rw [FR_size]; exact hi), FR_get hi]

theorem case_sums : ∀ i < 4, (((List.range 21).filter fun r => fusionCase r == i).map
    fun r => invFusionSizes.getD r 0).sum = caseCounts.getD i 0 := by decide +kernel

theorem cases_ok {i : Nat} (hi : i < 4) :
    (caseTabs FA i).Nodup ∧ (caseTabs FA i).length = caseCounts.getD i 0 := by
  unfold caseTabs
  have hL : ∀ r ∈ (List.range 21).filter (fun r => fusionCase r == i), r < 21 := fun r hr =>
    List.mem_range.1 (List.mem_filter.1 hr).1
  refine ⟨List.nodup_flatMap.2 ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [FA_get (hL r hr), FR_toList]
    refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    have hr' := hL r hr
    exact (Lr_inj (by omega) (List.mem_range.1 ha) (by omega) (List.mem_range.1 hb)
      (ET_inj (Lr_lt (by omega) (List.mem_range.1 ha)) (Lr_lt (by omega) (List.mem_range.1 hb)) e)).2
  · refine (List.nodup_range.filter _).imp_of_mem fun {a b} ha hb hne => ?_
    change List.Disjoint FA[a]!.tabs.toList FA[b]!.tabs.toList
    rw [FA_get (hL a ha), FA_get (hL b hb), FR_toList, FR_toList]
    intro x hxa hxb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hxa
    obtain ⟨j', hj', e⟩ := List.mem_map.1 hxb
    have ha' := hL a ha
    have hb' := hL b hb
    exact hne (Lr_inj (by omega) (List.mem_range.1 hj) (by omega) (List.mem_range.1 hj')
      (ET_inj (Lr_lt (by omega) (List.mem_range.1 hj)) (Lr_lt (by omega) (List.mem_range.1 hj'))
        e.symm)).1
  · rw [List.length_flatMap, ← case_sums i hi]
    congr 1
    refine List.map_congr_left fun r hr => ?_
    rw [FA_get (hL r hr), Array.length_toList, FR_size, cnt_fus (hL r hr)]

theorem facts2307 : sylowChecks sylowEnum fusionEnums = true := by
  rw [sylowEnum_eq.1, fusionEnums_eq]
  unfold sylowChecks
  simp only [ER_tabs, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact gens_ok
  · exact sylowEnum_eq.2
  · exact EA_size
  · exact inv_count
  · exact FA_size
  · exact allBelow_iff.2 fun r hr => by rw [FA_get hr]; exact rec_ok hr
  · exact allBelow_iff.2 fun r hr => allBelow_iff.2 fun r' hr' => by rw [FA_get hr]; exact notin_ok hr hr'
  · exact cover_ok
  · exact allBelow_iff.2 fun i hi => by
      rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact cases_ok hi

end CertificateChecks.KernelSpor.S2307

end
