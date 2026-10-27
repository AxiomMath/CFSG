
module

public import Certificates.Kernel.Sporadic.OddCore.HN2088K
public import Certificates.Kernel.Sporadic.OddCore.HN2089
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import CFSG.Certificates.Kernel.Spor.EnumBaseSound
public import CFSG.Certificates.Kernel.Spor.IdxBfsReplay
public import CFSG.Certificates.Kernel.Spor.CardBaseSep
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Spor.HNAOrbSound
public import CFSG.Sporadic.HNOddCore.ChainUtil
import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2088

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KS.PEnum CFSG.KS.BaseEq CFSG.KS.EnumBase CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.HN2089 CertificateChecks.KernelSpor.HND

theorem upk_size (P : Nat) : (unpack 800 10 P).size = 800 := by
  unfold unpack
  simp

theorem upk_get {P x : Nat} (hx : x < 800) : (unpack 800 10 P)[x]! = pg 10 (mask 10) P x := by
  unfold unpack
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem canon_lt {P x : Nat} (h : canonK 800 10 (mask 10) (800 * 10) P = true) (hx : x < 800) :
    pg 10 (mask 10) P x < 800 := by
  unfold canonK at h
  simp only [bAnd_iff] at h
  exact Nat.blt_eq.mp (allN_spec h.2.2 x hx)

theorem bp_lt : ∀ p ∈ bp, p < 800 := by
  intro p hp
  simp only [bp, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem g_get : pgenPerms.size = 14 ∧ ∀ g < 14, pgenPerms[g]! = unpack 800 10 (HPE.G g) := by
  rw [pg_eq]
  exact lines_bind (by decide +kernel) pgb

theorem g_canon (g : Nat) (hg : g < 14) : canonK 800 10 (mask 10) (800 * 10) (HPE.G g) = true :=
  allN_spec cG g hg

theorem g_perm (g : Nat) (hg : g < 14) :
    permOK 800 10 (mask 10) (800 * 10) (HPE.G g) (pinvS 800 10 (mask 10) (HPE.G g)) = true :=
  allN_spec pG g hg

theorem gi_get (g : Nat) (hg : g < 14) :
    (pinvs 800 pgenPerms)[g]! = unpack 800 10 (HPE.GI g) := by
  rw [pinvs_get (by rw [g_get.1]; exact hg), g_get.2 g hg, pinvCand_eq, invCand_unpack (g_perm g hg),
    Nat.eq_of_beq_eq_true (allN_spec gI g hg)]

theorem gi_canon (g : Nat) (hg : g < 14) : canonK 800 10 (mask 10) (800 * 10) (HPE.GI g) = true :=
  allN_spec cGI g hg

theorem g_inv (g : Nat) (hg : g < 14) :
    pisInv 800 pgenPerms[g]! (pinvs 800 pgenPerms)[g]! = true := by
  rw [pinvs_get (by rw [g_get.1]; exact hg), g_get.2 g hg, pisInv_eq, pinvCand_eq,
    invCand_unpack (g_perm g hg)]
  exact (invEqK_sound (g_perm g hg)).2

@[expose] noncomputable def EA : Array (Array Nat) :=
  Array.ofFn (n := 16384) fun i => unpack 800 10 (HPE.T i.val)

theorem EA_size : EA.size = 16384 := by simp [EA]

theorem EA_get {k : Nat} (hk : k < 16384) : EA[k]! = unpack 800 10 (HPE.T k) := by
  unfold EA
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem rec_get (k : Nat) (hk : k < 16384) : recK 800 10 (mask 10) 14 HPE.G HPE.T HPE.PL k = true :=
  sliceK_spec (S := 256) (by norm_num) (by norm_num) (fun s hs => rsK.all s hs) k hk

theorem par_size : parRecs.size = 16384 := by
  have h := par_shape
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem par_get (k : Nat) (hk : k < 16384) :
    pparOf parRecs k = parOf HPE.PL k ∧ plabOf parRecs k = labOf HPE.PL k := by
  have hl : HNT.PAR.E.length = 16384 := by
    have := par_size
    rw [par_eq] at this
    simpa using this
  have := parRK_spec HNT.PAR.E 0 parB k (by rw [hl]; exact hk)
  rw [Nat.zero_add] at this
  unfold pparOf plabOf
  rw [par_eq, List.getElem!_toArray]
  exact this

theorem T_canon : ∀ k < 16384, canonK 800 10 (mask 10) (800 * 10) (HPE.T k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have r := recK_spec (rec_get k hk)
    by_cases k0 : k = 0
    · subst k0
      rw [r.1 rfl]
      exact cI
    · obtain ⟨h1, h2, h3⟩ := r.2 k0
      rw [h3]
      exact canonK_pcomp (g_canon _ h2) (ih _ h1 (by omega))

theorem EA_zero : EA[0]! = pid 800 := by
  rw [EA_get (by norm_num), (recK_spec (rec_get 0 (by norm_num))).1 rfl, idK_sound idk, pid_eq]

theorem EA_rec (k : Nat) (hk : k < 16384) (k0 : k ≠ 0) :
    pparOf parRecs k < k ∧ plabOf parRecs k < 14 ∧
      EA[k]! = pcomp 800 pgenPerms[plabOf parRecs k]! EA[pparOf parRecs k]! := by
  rw [(par_get k hk).1, (par_get k hk).2]
  obtain ⟨h1, h2, h3⟩ := (recK_spec (rec_get k hk)).2 k0
  refine ⟨h1, h2, ?_⟩
  rw [EA_get hk, EA_get (by omega), g_get.2 _ h2, pcomp_eq,
    compA_unpack (g_canon _ h2) (T_canon _ (by omega)), ← h3]

theorem push_loop (m : Nat) (x0 : Array Nat) (f : Nat → Array (Array Nat) → Array Nat)
    (A : Nat → Array Nat) (h0 : x0 = A 0)
    (hf : ∀ j < m, ∀ E : Array (Array Nat), E.size = j + 1 → (∀ i < j + 1, E[i]! = A i) →
      f (1 + j) E = A (j + 1)) :
    Id.run (forIn (List.range' 1 m) #[x0]
      (fun k E => (pure (ForInStep.yield (E.push (f k E))) : Id (ForInStep (Array (Array Nat)))))) =
      Array.ofFn (n := m + 1) fun i => A i.val := by
  have := IdxBfs.forIn_range'_yield m 1 #[x0]
    (fun k E => (pure (ForInStep.yield (E.push (f k E))) : Id (ForInStep (Array (Array Nat)))))
    (fun j E => E.size = j + 1 ∧ ∀ i < j + 1, E[i]! = A i)
    (fun j hj E hP => ⟨E.push (f (1 + j) E), rfl, by simp [hP.1], fun i hi => by
      rcases Nat.lt_or_ge i (j + 1) with a | a
      · rw [IdxBfs.push_lt (by rw [hP.1]; exact a)]
        exact hP.2 i a
      · have e : i = E.size := by rw [hP.1]; omega
        subst e
        rw [IdxBfs.push_eq, hf j hj E hP.1 hP.2, hP.1]⟩)
    ⟨rfl, fun i hi => by
      have : i = 0 := by omega
      subst this
      rw [h0]
      rfl⟩
  obtain ⟨hs, hg⟩ := this
  apply Array.ext
  · rw [hs, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← getElem!_pos _ i h1]
    exact hg i (by rw [hs] at h1; exact h1)

theorem pEnum_eq : pEnum pgenPerms parRecs = EA := by
  have e : pEnum pgenPerms parRecs = Id.run (forIn (List.range' 1 16383) #[pid 800]
      (fun k E => (pure (ForInStep.yield (E.push
        (pcomp 800 pgenPerms[plabOf parRecs k]! E[pparOf parRecs k]!))) :
        Id (ForInStep (Array (Array Nat)))))) := by
    unfold pEnum
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, par_size]
    rfl
  rw [e, push_loop 16383 (pid 800) _ (fun k => EA[k]!) EA_zero.symm]
  · apply Array.ext
    · simp [EA_size]
    · intro i h1 h2
      rw [Array.getElem_ofFn, ← getElem!_pos EA i h2]
  · intro j hj E hs hE
    obtain ⟨h1, -, h3⟩ := EA_rec (1 + j) (by omega) (by omega)
    rw [hE _ (by omega), Nat.add_comm j 1, h3]

theorem pIdx_get {E : Array (Array Nat)}
    (hinj : ∀ a < E.size, ∀ b < E.size, E[a]! = E[b]! → a = b) {i : Nat} (hi : i < E.size)
    (d : Nat) : (pIdx E).getD E[i]! d = i := by
  unfold pIdx
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have := IdxBfs.forIn_range'_yield E.size 0 (∅ : Std.HashMap (Array Nat) Nat)
    (fun k m => (pure (ForInStep.yield (m.insert E[k]! k)) :
      Id (ForInStep (Std.HashMap (Array Nat) Nat))))
    (fun j m => ∀ i < j, m.getD E[i]! d = i)
    (fun j hj m hP => ⟨_, rfl, fun i hi' => ?_⟩) (fun i hi => absurd hi (Nat.not_lt_zero _))
  · exact this i hi
  · rw [Nat.zero_add, Std.HashMap.getD_insert]
    by_cases e : E[j]! = E[i]!
    · rw [ite_eq_left (beq_iff_eq.2 e), hinj j hj i (by omega) e]
    · rw [ite_eq_right (by simpa using e)]
      rcases Nat.lt_or_ge i j with a | a
      · exact hP i a
      · exact absurd (by rw [show i = j by omega]) e

theorem keyK_congr {ps : List Nat} {t u : Nat} (h : ∀ p ∈ ps, pg 10 (mask 10) t p = pg 10 (mask 10) u p) :
    keyK 800 10 ps t = keyK 800 10 ps u := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change Nat.add (pg 10 (mask 10) t p) (Nat.mul 800 (keyK 800 10 ps t)) =
      Nat.add (pg 10 (mask 10) u p) (Nat.mul 800 (keyK 800 10 ps u))
    rw [h p List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem p hq)]

theorem T_inj (i : Nat) (hi : i < 16384) (j : Nat) (hj : j < 16384)
    (h : ∀ p ∈ bp, pg 10 (mask 10) (HPE.T i) p = pg 10 (mask 10) (HPE.T j) p) : i = j :=
  keysSK_spec keys i hi j hj (keyK_congr h)

theorem EA_inj : ∀ a < EA.size, ∀ b < EA.size, EA[a]! = EA[b]! → a = b := by
  intro a ha b hb e
  rw [EA_size] at ha hb
  refine T_inj a ha b hb fun p hp => ?_
  rw [← upk_get (bp_lt p hp), ← upk_get (bp_lt p hp), ← EA_get ha, ← EA_get hb, e]

@[expose] noncomputable def H : Subgroup (Equiv.Perm (Fin 800)) := arrGen 800 pgenPerms

@[expose] def Mem (A : Array Nat) : Prop := A.size = 800 ∧ ∃ a ∈ H, PRep 800 A a

theorem mem_pcomp {A B : Array Nat} (hA : Mem A) (hB : Mem B) : Mem (pcomp 800 A B) := by
  obtain ⟨-, a, ha, pa⟩ := hA
  obtain ⟨-, b, hb, pb⟩ := hB
  exact ⟨by simp [CFSG.ONSchreier.Native.pcomp], a * b, H.mul_mem ha hb, prep_pcomp pa pb⟩

theorem mem_pid : Mem (pid 800) := ⟨by simp [pid], 1, H.one_mem, prep_pid⟩

theorem mem_g (g : Nat) (hg : g < 14) : Mem pgenPerms[g]! := by
  have hp := (prep_permOfArr (g_inv g hg)).1
  refine ⟨by rw [g_get.2 g hg, upk_size], permOfArr 800 pgenPerms[g]!, ?_, hp⟩
  exact Subgroup.subset_closure ⟨g, by rw [g_get.1]; exact hg, permOfArr_eq_of_prep hp⟩

theorem mem_gi (g : Nat) (hg : g < 14) : Mem (pinvs 800 pgenPerms)[g]! := by
  have hp := prep_permOfArr (g_inv g hg)
  refine ⟨by rw [gi_get g hg, upk_size], (permOfArr 800 pgenPerms[g]!)⁻¹, ?_, hp.2⟩
  exact H.inv_mem (Subgroup.subset_closure ⟨g, by rw [g_get.1]; exact hg,
    permOfArr_eq_of_prep hp.1⟩)

theorem mem_EA : ∀ k < 16384, Mem EA[k]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases k0 : k = 0
    · subst k0
      rw [EA_zero]
      exact mem_pid
    · obtain ⟨h1, h2, h3⟩ := EA_rec k hk k0
      rw [h3]
      exact mem_pcomp (mem_g _ h2) (ih _ h1 (by omega))

theorem pbar_nodup : QData.pbarBase.Nodup := by decide

theorem ch : chainCheck 800 pgenPerms QData.pbarWords QData.pbarBase QData.pbarSizes = true :=
  chainCheck_of ⟨g_get.1, fun j hj => by rw [g_get.2 j hj, Nat.eq_of_beq_eq_true (allN_spec hpc j hj)]⟩
    (by decide +kernel) (by decide +kernel) (by simp only [pbD, Array.toArray_toList])
    (by norm_num) (base_of (by decide +kernel) bPC) HPC.head HPC.hl (by decide +kernel) HPC.hs
    pPC (by decide +kernel)

theorem H_card : Nat.card H = 16384 := by
  unfold H
  rw [card_arrGen_of_chainCheck (by norm_num) pbar_nodup ch]
  rfl

@[expose] def bpF : List (Fin 800) := [0, 4, 3, 1, 2]

theorem bpF_mem : ∀ b ∈ bpF, (b : Nat) ∈ bp := by
  intro b hb
  simp only [bpF, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [bp]

theorem bp_memF : ∀ p ∈ bp, ∃ b ∈ bpF, (b : Nat) = p := by
  intro p hp
  simp only [bp, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by simp [bpF], rfl⟩
  · exact ⟨4, by simp [bpF], rfl⟩
  · exact ⟨3, by simp [bpF], rfl⟩
  · exact ⟨1, by simp [bpF], rfl⟩
  · exact ⟨2, by simp [bpF], rfl⟩

theorem sep {A B : Array Nat} (hA : Mem A) (hB : Mem B) (h : ∀ p ∈ bp, A[p]! = B[p]!) : A = B := by
  classical
  let ε : Nat → Equiv.Perm (Fin 800) := fun k =>
    if hk : k < 16384 then Classical.choose (mem_EA k hk).2 else 1
  have hε : ∀ k < 16384, ε k ∈ H ∧ PRep 800 EA[k]! (ε k) := fun k hk => by
    simp only [ε, dif_pos hk]
    exact Classical.choose_spec (mem_EA k hk).2
  obtain ⟨hAs, a, ha, pa⟩ := hA
  obtain ⟨hBs, b, hb, pb⟩ := hB
  have e : a = b := CFSG.KS.CardSep.eq_of_base H_card (fun k hk => (hε k hk).1) (B := bpF)
    (fun i hi j hj hij => T_inj i hi j hj fun p hp => by
      obtain ⟨b, hb, rfl⟩ := bp_memF p hp
      rw [← upk_get b.2, ← upk_get b.2, ← EA_get hi, ← EA_get hj, (hε i hi).2 b, (hε j hj).2 b,
        hij b hb]) ha hb
    (fun x hx => Fin.ext (by rw [← pa x, ← pb x]; exact h x (bpF_mem x hx)))
  apply Array.ext
  · rw [hAs, hBs]
  · intro i h1 h2
    have hi : i < 800 := by omega
    rw [← getElem!_pos A i h1, ← getElem!_pos B i h2, pa.apply hi, pb.apply hi, e]

theorem peq_self (A : Array Nat) : peq 800 A A = true :=
  allBelowN_iff.2 fun _ _ => beq_self_eq_true _

theorem left_eq {g k : Nat} (hg : g < 14) (hk : k < 16384) :
    r32 HPE.POS (k * 14 + g) < 16384 ∧
      pcomp 800 pgenPerms[g]! EA[k]! = EA[r32 HPE.POS (k * 14 + g)]! := by
  have hl := leftK_spec (sliceK_spec (S := 256) (by norm_num) (by norm_num)
    (fun s hs => lsK.all s hs) k hk) g hg
  refine ⟨hl.1, sep (mem_pcomp (mem_g g hg) (mem_EA k hk)) (mem_EA _ hl.1) fun p hp => ?_⟩
  have hp8 := bp_lt p hp
  rw [pcomp_get hp8, EA_get hk, upk_get hp8, g_get.2 g hg,
    upk_get (canon_lt (T_canon k hk) hp8), EA_get hl.1, upk_get hp8]
  exact hl.2 p hp

theorem conj_eq {g x y : Nat} (hg : g < 14) (hx : x < 16384) (hy : y < 16384)
    (h : ∀ p ∈ bp, pg 10 (mask 10) (HPE.G g) (pg 10 (mask 10) (HPE.T x)
      (pg 10 (mask 10) (HPE.GI g) p)) = pg 10 (mask 10) (HPE.T y) p) :
    pconj pgenPerms[g]! (pinvs 800 pgenPerms)[g]! EA[x]! = EA[y]! := by
  refine sep (mem_pcomp (mem_g g hg) (mem_pcomp (mem_EA x hx) (mem_gi g hg))) (mem_EA y hy)
    fun p hp => ?_
  have hp8 := bp_lt p hp
  have h1 := canon_lt (gi_canon g hg) hp8
  unfold pconj
  rw [pcomp_get hp8, pcomp_get hp8, gi_get g hg, upk_get hp8, EA_get hx, upk_get h1, g_get.2 g hg,
    upk_get (canon_lt (T_canon x hx) h1), EA_get hy, upk_get hp8]
  exact h p hp

theorem sq_iff {k : Nat} (hk : k < 16384) :
    peq 800 (pcomp 800 EA[k]! EA[k]!) (pid 800) = sqFixK 10 (mask 10) bp (HPE.T k) := by
  apply Bool.eq_iff_iff.2
  rw [sqFixK_iff]
  constructor
  · intro h p hp
    have hp8 := bp_lt p hp
    have := allBelowN_iff.1 h p hp8
    rw [beq_iff_eq, pcomp_get hp8, pid_get hp8, EA_get hk, upk_get hp8,
      upk_get (canon_lt (T_canon k hk) hp8)] at this
    exact this
  · intro h
    have e : pcomp 800 EA[k]! EA[k]! = pid 800 := by
      rw [← EA_zero]
      refine sep (mem_pcomp (mem_EA k hk) (mem_EA k hk)) (mem_EA 0 (by norm_num)) fun p hp => ?_
      have hp8 := bp_lt p hp
      rw [EA_zero, pcomp_get hp8, pid_get hp8, EA_get hk, upk_get hp8,
        upk_get (canon_lt (T_canon k hk) hp8)]
      exact h p hp
    rw [e]
    exact peq_self _

@[expose] noncomputable def O (c : Nat) : Nat := r32 HPF.O c
@[expose] noncomputable def cnt (c : Nat) : Nat := O (c + 1) - O c
@[expose] noncomputable def Lr (c j : Nat) : Nat := r32 HPF.L (O c + j)
@[expose] noncomputable def Pr (c j : Nat) : Nat := r32 HPF.P (O c + j)
@[expose] noncomputable def Gr (c j : Nat) : Nat := r32 HPF.G (O c + j)
@[expose] noncomputable def Qr (c j g : Nat) : Nat := r32 HPF.Q ((O c + j) * 14 + g)

@[expose] noncomputable def csR : Array (Array Nat × Array Nat × Array Nat) :=
  Array.ofFn (n := 29) fun c => (Array.ofFn (n := cnt c.val) fun j => Lr c.val j.val,
    Array.ofFn (n := cnt c.val) fun j => Pr c.val j.val,
    Array.ofFn (n := cnt c.val) fun j => Gr c.val j.val)

theorem cl_spec {c : Nat} (hc : c < 29) :
    0 < cnt c ∧ cnt c ≤ 16384 ∧ Pr c 0 = 0 ∧ Gr c 0 = 0 ∧
      sqFixK 10 (mask 10) bp (HPE.T (Lr c 0)) = true ∧
      ∀ j < cnt c, classPtK 10 (mask 10) bp 14 16384 HPE.G HPE.GI HPE.T (r32 HPF.L) (r32 HPF.P)
        (r32 HPF.G) (r32 HPF.Q) (r32 HPF.MK) (r32 HPF.PX) c (O c) (cnt c) j = true := by
  have h := classK_spec (clK.all c hc)
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h2, h3, h4, h5, h6, h7⟩

theorem Lr_lt {c j : Nat} (hc : c < 29) (hj : j < cnt c) : Lr c j < 16384 :=
  (classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).1

theorem Lr_mk {c j : Nat} (hc : c < 29) (hj : j < cnt c) : r32 HPF.MK (Lr c j) = c :=
  (classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).2.1

theorem Lr_px {c j : Nat} (hc : c < 29) (hj : j < cnt c) : r32 HPF.PX (Lr c j) = j :=
  (classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).2.2.1

@[expose] noncomputable def nx (i g : Nat) : Nat :=
  (pIdx EA).getD (pconj pgenPerms[g]! (pinvs 800 pgenPerms)[g]! EA[i]!) 16384

theorem lexK_iff {a b c d : Nat} : lexLtK a b c d = true ↔ IdxBfs.Lex a b c d := by
  unfold lexLtK IdxBfs.Lex
  rw [bIf_eq, bAnd_eq, blt_eq, beq_eq, blt_eq]
  by_cases h : a < c
  · simp [h]
  · simp [h]

theorem lex_of {a b c d : Nat} (h : lexLtK a b c d = true) : IdxBfs.Lex a b c d := lexK_iff.1 h

theorem not_lex_of {a b c d : Nat} (h : lexLtK a b c d = false) : ¬ IdxBfs.Lex a b c d := by
  intro hl
  have : lexLtK a b c d = true := lexK_iff.2 hl
  rw [h] at this
  exact absurd this Bool.false_ne_true

theorem tree_conj {c j : Nat} (hc : c < 29) (hj : j < cnt c) (j0 : j ≠ 0) :
    Pr c j < j ∧ Gr c j < 14 ∧
      pconj pgenPerms[Gr c j]! (pinvs 800 pgenPerms)[Gr c j]! EA[Lr c (Pr c j)]! = EA[Lr c j]! := by
  obtain ⟨h1, h2, h3⟩ := ((classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).2.2.2.1 j0)
  have h1' : Pr c j < j := h1
  have h2' : Gr c j < 14 := h2
  exact ⟨h1', h2', conj_eq h2' (Lr_lt hc (by omega)) (Lr_lt hc hj) h3.1⟩

theorem close_conj {c j g : Nat} (hc : c < 29) (hj : j < cnt c) (hg : g < 14) :
    Qr c j g < cnt c ∧
      pconj pgenPerms[g]! (pinvs 800 pgenPerms)[g]! EA[Lr c j]! = EA[Lr c (Qr c j g)]! ∧
      (Qr c j g = 0 ∨ ¬ IdxBfs.Lex j g (Pr c (Qr c j g)) (Gr c (Qr c j g))) := by
  obtain ⟨h1, h2, h3⟩ := (classPtK_spec ((cl_spec hc).2.2.2.2.2 j hj)).2.2.2.2 g hg
  have h1' : Qr c j g < cnt c := h1
  refine ⟨h1', conj_eq hg (Lr_lt hc hj) (Lr_lt hc h1') h2, ?_⟩
  rcases h3 with e | e
  · exact Or.inl e
  · exact Or.inr (not_lex_of e)

theorem nx_eq {i y g : Nat} (hg : g < 14) (hy : y < 16384)
    (h : pconj pgenPerms[g]! (pinvs 800 pgenPerms)[g]! EA[i]! = EA[y]!) : nx i g = y := by
  unfold nx
  rw [h]
  exact pIdx_get EA_inj (by rw [EA_size]; exact hy) 16384

theorem facts {c : Nat} (hc : c < 29) :
    IdxBfs.Facts 16384 14 (cnt c) nx (Lr c) (Pr c) (Gr c) (Qr c) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := cl_spec hc
  refine ⟨h1, h2, fun i hi => Lr_lt hc hi, fun a ha b hb e => ?_, h3, h4, fun i h0 hi => ?_,
    fun i h0 hi => ?_, fun h hh j hj => ?_⟩
  · rw [← Lr_px hc ha, ← Lr_px hc hb, e]
  · obtain ⟨a1, a2, a3⟩ := tree_conj hc hi (by omega)
    exact ⟨a1, a2, nx_eq a2 (Lr_lt hc hi) a3⟩
  · obtain ⟨-, -, -, a4⟩ := ((classPtK_spec ((cl_spec hc).2.2.2.2.2 i (by omega))).2.2.2.1
      (by omega))
    exact lex_of (a4 hi)
  · obtain ⟨a1, a2, a3⟩ := close_conj hc hh hj
    exact ⟨a1, nx_eq hj (Lr_lt hc a1) a2, a3⟩

theorem conjOrbit_eq (r : Nat) :
    conjOrbit (pIdx EA) EA pgenPerms (pinvs 800 pgenPerms) r = IdxBfs.idxBFS 16384 14 nx r := by
  have hs : pgenPerms.size = 14 := g_get.1
  unfold conjOrbit IdxBfs.idxBFS
  simp only [hs]
  rfl

theorem reps_get {c : Nat} (hc : c < 29) : pReps[c]! = Lr c 0 := by
  have hcl : clsLists.size = 29 := by rw [HN2093.clsLists_eq]; decide +kernel
  have e : pReps[c]! = (clsLists[c]!)[0]! := by
    unfold pReps
    rw [getElem!_pos _ c (by simpa using hcl ▸ hc), Array.getElem_map,
      ← getElem!_pos clsLists c (by rw [hcl]; exact hc)]
  rw [e, HN2093.clsLists_eq, lines_get]
  unfold Lr O
  rw [Nat.add_zero, Nat.eq_of_beq_eq_true (allN_spec reps c hc)]
  cases ClsT.E.getD c [] <;> rfl

theorem csR_get {c : Nat} (hc : c < 29) : csR[c]! = (Array.ofFn (n := cnt c) fun j => Lr c j.val,
    Array.ofFn (n := cnt c) fun j => Pr c j.val, Array.ofFn (n := cnt c) fun j => Gr c j.val) := by
  unfold csR
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem cs_eq : (pReps.map fun r => conjOrbit (pIdx EA) EA pgenPerms (pinvs 800 pgenPerms) r) =
    csR := by
  have hp : pReps.size = 29 := by
    unfold pReps
    rw [Array.size_map, HN2093.clsLists_eq]
    decide +kernel
  apply Array.ext
  · simp [csR, hp]
  · intro c h1 h2
    have hc : c < 29 := by simpa [csR] using h2
    rw [← getElem!_pos _ c h1, ← getElem!_pos csR c h2, csR_get hc]
    rw [getElem!_pos _ c h1, Array.getElem_map, ← getElem!_pos pReps c (by rw [hp]; exact hc),
      reps_get hc, conjOrbit_eq]
    exact IdxBfs.idxBFS_replay (facts hc)

theorem ofFn_get' {m : Nat} {f : Nat → Nat} {i : Nat} (hi : i < m) :
    (Array.ofFn (n := m) fun j => f j.val)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem mem_L {c x : Nat} : (Array.ofFn (n := cnt c) fun j => Lr c j.val).contains x = true ↔
    ∃ j < cnt c, Lr c j = x := by
  rw [Array.contains_iff_mem, Array.mem_ofFn]
  constructor
  · rintro ⟨j, e⟩
    exact ⟨j.val, j.isLt, e⟩
  · rintro ⟨j, hj, e⟩
    exact ⟨⟨j, hj⟩, e⟩

theorem forIn_list_yield {α β : Type} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (P : Nat → β → Prop)
    (h : ∀ j (hj : j < l.length), ∀ b, P j b →
      ∃ b', f l[j] b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P l.length (Id.run (forIn l init f)) := by
  induction l generalizing init P with
  | nil => simpa using h0
  | cons a l ih =>
    rw [List.forIn_cons]
    obtain ⟨b', hb, hP⟩ := h 0 (by simp) init h0
    rw [List.getElem_cons_zero] at hb
    rw [hb]
    have := ih b' (fun j b => P (j + 1) b) (fun j hj b hbj => by
      obtain ⟨b'', e, p⟩ := h (j + 1) (by simp only [List.length_cons]; omega) b hbj
      rw [List.getElem_cons_succ] at e
      exact ⟨b'', e, p⟩) hP
    simpa using this

theorem forIn_array_yield {α β : Type} (A : Array α) (init : β)
    (f : α → β → Id (ForInStep β)) (P : Nat → β → Prop)
    (h : ∀ j (hj : j < A.size), ∀ b, P j b →
      ∃ b', f A[j] b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P A.size (Id.run (forIn A init f)) := by
  have := forIn_list_yield A.toList init f P (fun j hj b hb => by
    obtain ⟨b', e, p⟩ := h j (by simpa using hj) b hb
    exact ⟨b', by rw [Array.getElem_toList]; exact e, p⟩) h0
  rwa [Array.length_toList, Array.forIn_toList] at this

theorem classMarks_spec (Ls : Array (Array Nat)) :
    (classMarks Ls).size = 16384 ∧ ∀ k < 16384, (∃ c < Ls.size, k ∈ Ls[c]!) →
      (classMarks Ls)[k]! < Ls.size ∧ k ∈ Ls[(classMarks Ls)[k]!]! := by
  unfold classMarks
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have := IdxBfs.forIn_range'_yield Ls.size 0 (Array.replicate 16384 29)
    (fun c mk => (pure (ForInStep.yield (Id.run (forIn Ls[c]! mk
      (fun k mk => (pure (ForInStep.yield (mk.set! k c)) : Id (ForInStep (Array Nat))))))) :
      Id (ForInStep (Array Nat))))
    (fun c mk => mk.size = 16384 ∧ ∀ k < 16384, (∃ c' < c, k ∈ Ls[c']!) →
      mk[k]! < c ∧ k ∈ Ls[mk[k]!]!)
    (fun c hc mk hP => ⟨_, rfl, ?_⟩) ⟨by simp, fun k _ ⟨c', hc', _⟩ => absurd hc' (by omega)⟩
  · refine ⟨this.1, fun k hk hm => ?_⟩
    have := this.2 k hk hm
    exact this
  · rw [Nat.zero_add]
    have hin := forIn_array_yield Ls[c]! mk
      (fun k mk => (pure (ForInStep.yield (mk.set! k c)) : Id (ForInStep (Array Nat))))
      (fun t mk' => mk'.size = 16384 ∧ ∀ k < 16384,
        ((∃ c' < c, k ∈ Ls[c']!) ∨ ∃ i, ∃ hi : i < Ls[c]!.size, i < t ∧ (Ls[c]!)[i] = k) →
          mk'[k]! < c + 1 ∧ k ∈ Ls[mk'[k]!]!)
      (fun t ht mk' hQ => ⟨_, rfl, by rw [Array.size_set!]; exact hQ.1, fun k hk hm => ?_⟩)
      ⟨hP.1, fun k hk hm => by
        rcases hm with hm | ⟨i, hi, h0, -⟩
        · have := hP.2 k hk hm
          exact ⟨by omega, this.2⟩
        · omega⟩
    · refine ⟨hin.1, fun k hk ⟨c', hc', hkm⟩ => ?_⟩
      rcases Nat.lt_or_ge c' c with a | a
      · exact hin.2 k hk (Or.inl ⟨c', a, hkm⟩)
      · have e : c' = c := by omega
        subst e
        obtain ⟨i, hi, hik⟩ := Array.mem_iff_getElem.1 hkm
        exact hin.2 k hk (Or.inr ⟨i, hi, hi, hik⟩)
    · rw [IdxBfs.set_get (by rw [hQ.1]; exact hk)]
      by_cases e : (Ls[c]!)[t] = k
      · rw [if_pos e]
        refine ⟨by omega, ?_⟩
        rw [← e]
        exact Array.getElem_mem ht
      · rw [if_neg e]
        refine hQ.2 k hk ?_
        rcases hm with hm | ⟨i, hi, h0, hik⟩
        · exact Or.inl hm
        · refine Or.inr ⟨i, hi, ?_, hik⟩
          rcases Nat.lt_or_ge i t with a | a
          · exact a
          · have : i = t := by omega
            subst this
            exact absurd hik e

theorem cnt_lt (c : Nat) (hc : c < 29) : 0 < cnt c := (cl_spec hc).1

theorem classOK_true {c : Nat} (hc : c < 29) :
    classOK (pIdx EA) EA pgenPerms (pinvs 800 pgenPerms) (Lr c 0)
      (Array.ofFn (n := cnt c) fun j => Lr c j.val) (Array.ofFn (n := cnt c) fun j => Pr c j.val)
      (Array.ofFn (n := cnt c) fun j => Gr c j.val) = true := by
  obtain ⟨h1, h2, -, -, -, -⟩ := cl_spec hc
  unfold classOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, Array.size_ofFn,
    allBelowN_iff]
  refine ⟨⟨⟨⟨⟨⟨h2, h1⟩, ofFn_get' h1⟩, trivial⟩, trivial⟩, fun j hj => ?_⟩, fun j hj g hg => ?_⟩
  · rw [ofFn_get' hj]
    refine ⟨Lr_lt hc hj, ?_⟩
    by_cases j0 : j = 0
    · exact Or.inl j0
    · right
      obtain ⟨a1, a2, a3⟩ := tree_conj hc hj j0
      rw [ofFn_get' hj, ofFn_get' hj, ofFn_get' (by omega : Pr c j < cnt c), a3]
      exact ⟨⟨a1, a2⟩, peq_self _⟩
  · obtain ⟨a1, a2, -⟩ := close_conj hc hj hg
    rw [ofFn_get' hj, a2, pIdx_get EA_inj (by rw [EA_size]; exact Lr_lt hc a1)]
    exact ⟨⟨Lr_lt hc a1, peq_self _⟩, mem_L.2 ⟨_, a1, rfl⟩⟩

theorem words_ok : ∀ i < 14, plettersOK 11 pWords[i]! = true ∧
    peq 800 (pword 800 s4Perms (pinvs 800 s4Perms) pWords[i]!) pgenPerms[i]! = true ∧
    pisInv 800 pgenPerms[i]! (pinvs 800 pgenPerms)[i]! = true := by
  have hl : ∀ i < 14, plettersOK 11 pWords[i]! = true := by decide +kernel
  intro i hi
  refine ⟨hl i hi, ?_, g_inv i hi⟩
  have hw := wordEqK_sound (r := HPE.G i) s_get pS (allN_spec wP i hi)
  have hc := g_canon i hi
  rw [peq_eq, pword_eq_wordA, pinvs_eq_rawInvs, hw.1, g_get.2 i hi, eqA_unpack hc hc]
  exact Nat.beq_refl _

theorem left_get (g k : Nat) (hg : g < 14) (hk : k < 16384) :
    (pleftTabs[g]!)[k]! = r32 HPE.POS (k * 14 + g) := by
  have hlen : (HNT.PL.E.getD g []).length = 16384 := by
    have h := pl_shape
    rw [pl_eq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have := (Array.all_eq_true.1 h.2) g (by rw [h.1]; exact hg)
    have hsz : (((HNT.PL.E.map List.toArray).toArray)[g]!).size = 16384 := by
      rw [getElem!_pos _ g (by rw [h.1]; exact hg)]
      exact beq_iff_eq.1 this
    rw [lines_get] at hsz
    simpa using hsz
  rw [pl_eq, lines_get, List.getElem!_toArray,
    posRK_spec (HNT.PL.E.getD g []) 0 (allN_spec posB g hg) k (by rw [hlen]; exact hk),
    Nat.zero_add]

theorem left_size : pleftTabs.size = 14 := by
  have h := pl_shape
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem marks_size : (classMarks (csR.map (·.1))).size = 16384 :=
  (classMarks_spec _).1

theorem csR_fst {c : Nat} (hc : c < 29) :
    ((csR.map (·.1))[c]!) = Array.ofFn (n := cnt c) fun j => Lr c j.val := by
  rw [getElem!_pos _ c (by simpa [csR] using hc), Array.getElem_map,
    ← getElem!_pos csR c (by simpa [csR] using hc), csR_get hc]

theorem checksE_ok : sylowChecksE s4Perms pgenPerms parRecs EA = true := by
  unfold sylowChecksE
  simp only []
  rw [cs_eq]
  unfold sylowChecksH
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  have hcs : csR.size = 29 := by simp [csR]
  have hp : pReps.size = 29 := by
    unfold pReps
    rw [Array.size_map, HN2093.clsLists_eq]
    decide +kernel
  have hsq : ∀ k < 16384, peq 800 (pcomp 800 EA[k]! EA[k]!) (pid 800) = true →
      ∃ c < 29, k ∈ (csR.map (·.1))[c]! := by
    intro k hk h
    rw [sq_iff hk] at h
    obtain ⟨a1, a2, a3⟩ := coverK_spec (sliceK_spec (S := 16) (by norm_num) (by norm_num)
      (fun s hs => cvK.all s hs) k hk) h
    refine ⟨_, a1, ?_⟩
    rw [csR_fst a1, ← Array.contains_iff_mem, mem_L]
    exact ⟨_, a2, a3⟩
  refine ⟨s_get.1, g_get.1, by decide +kernel, ?_, par_size, EA_size, by rw [EA_zero]; exact peq_self _,
    ?_, left_size, ?_, ch, ?_, hp, hcs, marks_size, ?_, ?_, ?_⟩
  · exact allBelowN_iff.2 fun i hi => by
      obtain ⟨a1, a2, a3⟩ := words_ok i hi
      rw [a1, a2, a3]
      rfl
  · refine allBelowN_iff.2 fun k hk => ?_
    by_cases k0 : k = 0
    · simp [k0]
    · obtain ⟨a1, a2, a3⟩ := EA_rec k hk k0
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨⟨a1, a2⟩, by rw [a3]; exact peq_self _⟩
  · refine allBelowN_iff.2 fun g hg => allBelowN_iff.2 fun k hk => ?_
    obtain ⟨a1, a2⟩ := left_eq hg hk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [left_get g k hg hk, a2]
    exact ⟨a1, peq_self _⟩
  · have e : (List.range 16384).countP (fun k => peq 800 (pcomp 800 EA[k]! EA[k]!) (pid 800)) =
        (List.range 16384).countP (fun k => sqFixK 10 (mask 10) bp (HPE.T k)) :=
      List.countP_congr fun k hk => by rw [sq_iff (List.mem_range.1 hk)]
    rw [e, ← cntN_eq]
    exact Nat.eq_of_beq_eq_true sqCnt
  · refine allBelowN_iff.2 fun c hc => ?_
    rw [Bool.and_eq_true, reps_get hc, sq_iff (Lr_lt hc (cnt_lt c hc)), csR_get hc]
    exact ⟨(cl_spec hc).2.2.2.2.1, classOK_true hc⟩
  · refine allBelowN_iff.2 fun c hc => allBelowN_iff.2 fun c' hc' => ?_
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    by_cases e : c = c'
    · exact Or.inl e
    · right
      rw [csR_get hc', reps_get hc, Bool.eq_false_iff]
      intro hm
      obtain ⟨j, hj, hjx⟩ := mem_L.1 hm
      have := Lr_mk hc' hj
      rw [hjx, Lr_mk hc (cnt_lt c hc)] at this
      exact e this
  · refine allBelowN_iff.2 fun k hk => ?_
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq]
    by_cases hs : peq 800 (pcomp 800 EA[k]! EA[k]!) (pid 800) = true
    · right
      obtain ⟨b1, b2⟩ := (classMarks_spec (csR.map fun x => x.1)).2 k hk
        (by simpa [hcs] using hsq k hk hs)
      have b1' : (classMarks (csR.map fun x => x.1))[k]! < 29 := by simpa [hcs] using b1
      refine ⟨b1', ?_⟩
      have e : csR[(classMarks (csR.map fun x => x.1))[k]!]!.1 =
          (csR.map fun x => x.1)[(classMarks (csR.map fun x => x.1))[k]!]! := by
        rw [getElem!_pos (csR.map fun x => x.1) _ (by rw [Array.size_map, hcs]; exact b1'),
          Array.getElem_map, ← getElem!_pos csR _ (by rw [hcs]; exact b1')]
      rw [e, Array.contains_iff_mem]
      exact b2
    · left
      exact Bool.eq_false_iff.2 hs

theorem facts2088 : sylowChecks = true := by
  unfold sylowChecks
  rw [pEnum_eq]
  exact checksE_ok

end CertificateChecks.KernelSpor.HN2088

end
