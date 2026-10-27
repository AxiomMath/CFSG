module

public import Certificates.Data.D4HexLocCheck
public import Certificates.Kernel.S63K.P4237F
public import Certificates.Kernel.S63K.PChecksP
public import Certificates.Kernel.S63K.A21112
public import CFSG.Certificates.Kernel.S63K.ClassBfsSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.P4237

open CFSG.D4Hex CFSG.LargeExtraspecial.S63 CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KS.SporSch.M24
  CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelS63
  CertificateChecks.KernelS63.PD

theorem memC_eq {G P PAR LAB W S : ℕ → ℕ} {ng N : ℕ} (hK : ClassK G P PAR LAB W S ng N) (Y : ℕ) :
    memR (ElG P N) (lookup (mkIdx (ElG P N))) (unpackR 24 Y) =
      (List.range N).any fun w => eqM (P w) Y := by
  have hsz : (ElG P N).size = N := by simp [ElG]
  cases ha : (List.range N).any fun w => eqM (P w) Y
  · unfold memR
    cases hm : (decide (lookup (mkIdx (ElG P N)) (unpackR 24 Y) < (ElG P N).size) &&
        (ElG P N)[lookup (mkIdx (ElG P N)) (unpackR 24 Y)]! == unpackR 24 Y)
    · rfl
    · exfalso
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz] at hm
      obtain ⟨hk, he⟩ := hm
      rw [elG_get hk] at he
      have : ((List.range N).any fun w => eqM (P w) Y) = true :=
        List.any_eq_true.2 ⟨_, List.mem_range.2 hk, eqM_iff.2 he⟩
      rw [ha] at this
      exact Bool.false_ne_true this
  · obtain ⟨w, hw, he⟩ := List.any_eq_true.1 ha
    have hw' := List.mem_range.1 hw
    rw [← eqM_iff.1 he]
    unfold memR
    rw [idx_of_C hK hw', elG_get hw', hsz]
    simp [hw']

noncomputable abbrev CZ : ClassData := CkG ID.ZP LK.PAR LK.LAB 819

theorem cz_T {i : ℕ} (hi : i < 819) : CZ.T[i]! = unpackR 24 (ID.ZP i) := elG_get hi

theorem zp_lt : ∀ i < 819, ID.ZP i < 2 ^ 576 := (bfsDistK_sound I21111.zdist).1

theorem cz_mem (Y : ℕ) : memR CZ.T CZ.idx (unpackR 24 Y) =
    (List.range 819).any fun w => eqM (ID.ZP w) Y := memC_eq L4234.hK Y

theorem cz_mem_one {Y : ℕ} (h : memS ID.ZP ID.ZS 819 Y = 1) : memR CZ.T CZ.idx (unpackR 24 Y) = true := by
  obtain ⟨w, hw, he⟩ := memS_one I21111.zdist h
  rw [cz_mem]
  exact List.any_eq_true.2 ⟨w, List.mem_range.2 hw, by rw [he]; exact eqM_self _⟩

theorem cz_mem_zero {Y : ℕ} (hY : Y < 2 ^ 576) (h : memS ID.ZP ID.ZS 819 Y = 0) :
    memR CZ.T CZ.idx (unpackR 24 Y) = false := by
  rw [cz_mem, List.any_eq_false]
  intro w hw
  have hw' := List.mem_range.1 hw
  rw [H4240.eqM_lt (zp_lt w hw') hY]
  simpa [Nat.beq_eq] using memS_zero I21111.zdist h w hw'

theorem kz : ClassK CD.CG ZCP ZCPar ZCLab ZCW ZCS 4 3 ∧ ZCP 0 = ID.ZP 0 := classK_of_bfsK zcbfs

theorem ku : ClassK CD.CG UCP UCPar UCLab UCW UCS 4 24 ∧ UCP 0 = U0 0 := classK_of_bfsK ucbfs

theorem czC_eq : mkClass cGens z0R = CkG ZCP ZCPar ZCLab 3 :=
  mkClass_of_K C21113.cg_size C21113.cg_eq (by rw [kz.2, L4234.z0_eq]) kz.1

theorem cu_eq : mkClass cGens (wordR d4Gens locU0Word) = CkG UCP UCPar UCLab 24 :=
  mkClass_of_K C21113.cg_size C21113.cg_eq (by rw [ku.2, u0_eq]) ku.1

theorem t0_eq : t0R = unpackR 24 T0r := by rw [C21113.t0_eq, unpackR_mod, T0r]

theorem dk_size : C21113.Dk.El.size = 3072 := by simp [C21113.Dk, C21113.El]

theorem inV_ok {k X : ℕ} (hk : k < 4) (h : inV k X = true) :
    (conjI cGens[k]! cGens[k]! (unpackR 24 X) == z0R ||
      conjI cGens[k]! cGens[k]! (unpackR 24 X) == CZ.T[1]! ||
      conjI cGens[k]! cGens[k]! (unpackR 24 X) == CZ.T[5]!) = true := by
  unfold inV mw at h
  rw [sB, bIf_eq, bIf_eq] at h
  rw [C21113.cg_eq k hk, conjI, mulR_unpackR, mulR_unpackR, L4234.z0_eq, cz_T (by norm_num),
    cz_T (by norm_num), beq_eq, beq_eq, beq_eq]
  split at h
  · rename_i h1
    rw [h1]
    rfl
  · split at h
    · rename_i h2
      rw [h2, Bool.or_true, Bool.true_or]
    · rw [h, Bool.or_true]

theorem vCheck : locVCheck CZ C21113.Dk (CkG ZCP ZCPar ZCLab 3) = true := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
    v20, v21⟩ := vparts
  have z1 := cz_T (i := 1) (by norm_num)
  have z5 := cz_T (i := 5) (by norm_num)
  unfold locVCheck
  simp only [Bool.and_eq_true]
  and_intros
  · exact C21113.gens_ok
  · exact List.all_eq_true.2 fun k hk => allLt_iff.1 C21113.comm_ok k (List.mem_range.1 hk)
  · exact C21113.ok_eq
  · rw [cz_T (by norm_num), L4234.z0_eq]
    exact beq_self_eq_true _
  · rw [z1, isInv_eq]
    exact v3
  · rw [z5, isInv_eq]
    exact v4
  · rw [z1, z5, L4234.z0_eq, mulR_unpackR, beq_eq]
    exact v5
  · rw [z1, z5, L4234.z0_eq, mulR_unpackR, beq_eq]
    exact v6
  · rw [z1, z5, L4234.z0_eq, mulR_unpackR, beq_eq]
    exact v7
  · rw [z1, z5, L4234.z0_eq, mulR_unpackR, beq_eq]
    exact v8
  · rw [z1, z5, L4234.z0_eq, mulR_unpackR, beq_eq]
    exact v9
  · rw [z1, z5, L4234.z0_eq, mulR_unpackR, beq_eq]
    exact v10
  · rw [t0_eq, L4234.z0_eq, comm_eq]
    exact v11
  · rw [t0_eq, z1, comm_eq]
    exact v12
  · rw [t0_eq, z5, comm_eq]
    exact v13
  · refine List.all_eq_true.2 fun k hk => ?_
    have hk' : k < 4 := by
      have := List.mem_range.1 hk
      rwa [C21113.cg_size] at this
    have h := MatL.allN_iff.1 v14 k hk'
    rw [bAnd_eq', bAnd_eq', Bool.and_eq_true, Bool.and_eq_true] at h
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_⟩
    · have := inV_ok hk' h.1
      rwa [← L4234.z0_eq] at this
    · have := inV_ok hk' h.2.1
      rwa [← z1] at this
    · have := inV_ok hk' h.2.2
      rwa [← z5] at this
  · exact classTreeOK_of_K C21113.cg_size C21113.cg_eq (by rw [kz.2, L4234.z0_eq]) kz.1
  · rw [z1]
    exact (memC_eq kz.1 _).trans v15
  · rw [z5]
    exact (memC_eq kz.1 _).trans v16
  · have hq : VC 0 < 3072 := Nat.blt_eq.mp v17
    refine List.any_eq_true.2 ⟨VC 0, List.mem_range.2 (by rw [dk_size]; exact hq), ?_⟩
    change (locComm C21113.El[VC 0]! z0R && locComm C21113.El[VC 0]! CZ.T[1]! &&
      locComm C21113.El[VC 0]! CZ.T[5]! &&
      (mulR C21113.El[VC 0]! C21113.El[VC 0]! == z0R ||
        mulR C21113.El[VC 0]! C21113.El[VC 0]! == CZ.T[1]! ||
        mulR C21113.El[VC 0]! C21113.El[VC 0]! == CZ.T[5]!)) = true
    rw [C21113.el_get hq, z1, z5, L4234.z0_eq, comm_eq, comm_eq, comm_eq, v18, v19, v20,
      mulR_unpackR, beq_eq, beq_eq, beq_eq]
    rw [sB, bIf_eq, bIf_eq] at v21
    unfold mw at v21
    split at v21
    · rename_i h1
      rw [h1]
      rfl
    · split at v21
      · rename_i h2
        rw [h2]
        simp
      · rw [v21]
        simp

#kc_forall_tree uAll (fun b => CertificateChecks.KernelS63.PD.ch4237U b = true) 13
  CertificateChecks.KernelS63.PD.ch4237U
#kc_forall_tree pAll (fun b => CertificateChecks.KernelS63.PD.ch4237P b = true) 31
  CertificateChecks.KernelS63.PD.ch4237P

theorem fu_all : ∀ i < 819, fuK i = true :=
  fun i hi => I21111.blocks (f := fuK) (n := 63) (m := 13) (fun b hb => uAll b hb) (by norm_num) i
    (by omega)

theorem pa_all : ∀ h < 2464, ∀ j < 12, paK h j = true := by
  intro h hh j hj
  have := I21111.blocks (f := fun h => bIf(Nat.blt h 2464, allN 12 fun j => paK h j, true))
    (n := 81) (m := 31) (fun b hb => pAll b hb) (by norm_num) h (by omega)
  rw [bIf_eq, if_pos (Nat.blt_eq.mpr hh)] at this
  exact MatL.allN_iff.1 this j hj

theorem beq_nat' (a b : ℕ) : (a == b) = Nat.beq a b := HD.beq_nat a b

theorem cw_ok : cWords.all (fun w => w.all (fun k => decide (k < 8)) &&
    fixesLine0 (locWordArr w)) = true := by
  refine List.all_eq_true.2 fun w hw => ?_
  have h := List.all_eq_true.1 cwfix w hw
  simp only [stepOKK, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
  have hw8 : ∀ k ∈ w, k < 8 := fun k hk => by
    simpa using List.all_eq_true.1 h.1 k hk
  rw [Bool.and_eq_true]
  refine ⟨h.1, ?_⟩
  unfold fixesLine0
  rw [(H4240.word_get w hw8 0 (by norm_num)).1, (H4240.word_get w hw8 1 (by norm_num)).1,
    (H4240.word_get w hw8 5 (by norm_num)).1]
  exact h.2

theorem steps_ok : locStepWords.all locStepOK = true := by
  refine List.all_eq_true.2 fun s hs => ?_
  have h := List.all_eq_true.1 steps s hs
  unfold stepOKK at h
  unfold locStepOK
  rw [Bool.and_eq_true] at h ⊢
  have hw8 : ∀ k ∈ s.2, k < 8 := fun k hk => by
    simpa using List.all_eq_true.1 h.1 k hk
  refine ⟨h.1, ?_⟩
  unfold fixesLine0
  rw [(H4240.word_get s.2 hw8 0 (by norm_num)).1, (H4240.word_get s.2 hw8 1 (by norm_num)).1,
    (H4240.word_get s.2 hw8 5 (by norm_num)).1, beq_nat']
  exact h.2

theorem dq_size : A21112.DQ.El.size = 512 := by simp [A21112.DQ, DkG, ElG]

theorem qpdist : bfsDistK AD.QP AD.QS 512 = true := (bfsK_sound AD.repQ).2.2.2.2.1

theorem memQ_one {Y : ℕ} (h : memS AD.QP AD.QS 512 Y = 1) :
    memR A21112.DQ.El A21112.DQ.idx (unpackR 24 Y) = true := by
  obtain ⟨w, hw, he⟩ := memS_one qpdist h
  rw [A21112.memQ_eq]
  exact List.any_eq_true.2 ⟨w, List.mem_range.2 hw, by rw [he]; exact eqM_self _⟩

theorem memQ_zero {Y : ℕ} (hY : Y < 2 ^ 576) (h : memS AD.QP AD.QS 512 Y = 0) :
    memR A21112.DQ.El A21112.DQ.idx (unpackR 24 Y) = false := by
  rw [A21112.memQ_eq]
  unfold AD.memQ
  rw [List.any_eq_false]
  intro w hw
  have hw' := List.mem_range.1 hw
  rw [H4240.eqM_lt (H4240.q_lt w hw') hY]
  simpa [Nat.beq_eq] using memS_zero qpdist h w hw'

theorem fuse_all : (allLt 819 fun i => !(locComm CZ.T[i]! t0R) || i == 0 || i == 1 || i == 5 ||
    memR (CkG UCP UCPar UCLab 24).T (CkG UCP UCPar UCLab 24).idx CZ.T[i]!) = true := by
  refine allLt_iff.2 fun i hi => ?_
  have h := fu_all i hi
  unfold fuK at h
  rw [cz_T hi, t0_eq, comm_eq, beq_nat', beq_nat', beq_nat']
  change (!cmP (ID.ZP i) T0r || Nat.beq i 0 || Nat.beq i 1 || Nat.beq i 5 ||
    memR (ElG UCP 24) (lookup (mkIdx (ElG UCP 24))) (unpackR 24 (ID.ZP i))) = true
  rw [memC_eq ku.1]
  revert h
  generalize cmP (ID.ZP i) T0r = a
  generalize Nat.beq i 0 = b
  generalize Nat.beq i 1 = c
  generalize Nat.beq i 5 = d
  generalize ((List.range 24).any fun w => eqM (UCP w) (ID.ZP i)) = e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem qa_lt : ∀ i < 2464, QA i < 4096 ∧ QB i < 4096 := fun i hi => by
  have h := MatL.allN_iff.1 qbound i hi
  rw [bAnd_eq', Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.blt_eq.mp h.2⟩

theorem q_inj : ∀ a < 2464, ∀ b < 2464, QA a = QA b → QB a = QB b → a = b := by
  intro a ha b hb e1 e2
  refine (bfsDistK_sound PD.qdist).2 a ha b hb ?_
  unfold qcode
  rw [e1, e2]

theorem pact : PAct DT QA QB QW 2464 := by
  intro h hh j hj
  rw [locSteps_size] at hj ⊢
  have hp := pa_all h hh j hj
  unfold paK at hp
  rw [sB, sB, bIf_eq] at hp
  rw [locY_eq hj (qa_lt h hh).1, locY_eq hj (qa_lt h hh).2]
  split at hp
  · rename_i hc
    rw [bAnd_eq', bAnd_eq', Bool.and_eq_true, Bool.and_eq_true] at hc
    have hw : QW (12 * h + j) < 2464 := Nat.blt_eq.mp hc.1
    left
    rw [← beqT hc.2.1, ← beqT hc.2.2]
    exact ⟨memT_pt (qa_lt _ hw).1, memT_pt (qa_lt _ hw).2, dt_idx (qa_lt _ hw).1,
      dt_idx (qa_lt _ hw).2⟩
  · rw [bAnd_eq', Bool.and_eq_true, bIf_eq] at hp
    right
    refine ⟨?_, beqT hp.1⟩
    split at hp
    · rename_i h0
      rw [memT_of_zero (Y := cjS j (HD.TP (QA h))) (mod_lt' _) (beqT h0), Bool.false_and]
    · rw [memT_of_zero (Y := cjS j (HD.TP (QB h))) (mod_lt' _) (beqT hp.2), Bool.and_false]

theorem qrun' : orbRunK QW QPa QLa locSteps.size (2464 + 1) 0 1 = 2464 := by
  rw [locSteps_size]
  exact beqT qrun

theorem pforest : locPairForest DT (QA 0, QB 0) =
      ((List.range' 1 (2464 - 1)).map fun i => ((QA i, QB i), (QA (QPa i), QB (QPa i)), QLa i)) ∧
    PTree DT QA QB QPa QLa 2464 :=
  locPairForest_of_K (by norm_num) q_inj pact qrun'

theorem pgo_of_tree : ∀ m k (seen : List (ℕ × ℕ)), k + m = 2464 → 1 ≤ k →
    (∀ i < k, seen.contains (QA i, QB i)) →
    locPairGo DT seen ((List.range' k m).map fun i =>
      ((QA i, QB i), (QA (QPa i), QB (QPa i)), QLa i)) = true := by
  intro m
  induction m with
  | zero => intro k seen _ _ _; rfl
  | succ m ih =>
    intro k seen hk h1 hs
    rw [List.range'_succ, List.map_cons]
    obtain ⟨hp, hl, hma, hmb, hia, hib⟩ := pforest.2 k h1 (by omega)
    unfold locPairGo
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have hka : QA k < DT.El.size := by
      rw [dt_size]
      exact (qa_lt k (by omega)).1
    have hkb : QB k < DT.El.size := by
      rw [dt_size]
      exact (qa_lt k (by omega)).2
    refine ⟨⟨⟨⟨⟨⟨hs _ hp, hl⟩, hka⟩, hkb⟩, ?_⟩, ?_⟩, ?_⟩
    · unfold memR at hma
      simp only [Bool.and_eq_true, beq_iff_eq] at hma
      rw [← hia]
      exact beq_iff_eq.2 hma.2.symm
    · unfold memR at hmb
      simp only [Bool.and_eq_true, beq_iff_eq] at hmb
      rw [← hib]
      exact beq_iff_eq.2 hmb.2.symm
    · refine ih (k + 1) _ (by omega) (by omega) fun i hi' => ?_
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
      · rw [List.contains_cons, hs i hi', Bool.or_true]
      · rw [List.contains_cons, beq_self_eq_true, Bool.true_or]

theorem pairChain : locPairChain DT A21112.DQ (wordR d4Gens locU0Word) = true := by
  have hr := qroot
  rw [bAnd_eq', Bool.and_eq_true] at hr
  have hu : wordR d4Gens locU0Word = unpackR 24 (HD.TP (QA 0)) := by rw [u0_eq, beqT hr.1]
  have ht : t0R = unpackR 24 (HD.TP (QB 0)) := by rw [t0_eq, beqT hr.2]
  have h0 := qa_lt 0 (by norm_num)
  have i0 : DT.idx (wordR d4Gens locU0Word) = QA 0 := by rw [hu, dt_idx h0.1]
  have i1 : DT.idx t0R = QB 0 := by rw [ht, dt_idx h0.2]
  have hk := qk
  rw [bAnd_eq', bAnd_eq', Bool.and_eq_true, Bool.and_eq_true] at hk
  have hkl : QK 0 < 2464 := Nat.blt_eq.mp hk.1
  unfold locPairChain
  simp only [i0, i1, pforest.1, Bool.and_eq_true, decide_eq_true_eq, dt_size, beq_iff_eq]
  refine ⟨⟨⟨⟨h0.1, ?_⟩, h0.2⟩, ?_⟩, ?_, ?_⟩
  · rw [dt_el h0.1, hu]
  · rw [dt_el h0.2, ht]
  · exact pgo_of_tree _ 1 _ (by norm_num) le_rfl fun i hi => by
      obtain rfl : i = 0 := by omega
      simp
  · refine List.any_eq_true.2 ⟨(QA (QK 0), QB (QK 0)), ?_, ?_⟩
    · by_cases e : QK 0 = 0
      · rw [e]
        exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨QK 0,
          List.mem_range'.2 ⟨QK 0 - 1, by omega, by omega⟩, rfl⟩, rfl⟩)
    · have hl := qa_lt _ hkl
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true']
      refine ⟨⟨⟨hl.1, hl.2⟩, ?_⟩, ?_⟩
      · rw [dt_el hl.1, beqT hk.2.1, L4234.z0_eq]
      · rw [dt_el hl.2]
        exact memQ_zero (H4240.t_lt _ hl.2) (beqT hk.2.2)

theorem fusion : locFusion CZ (CkG UCP UCPar UCLab 24) DT A21112.DQ = true := by
  unfold locFusion
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨cw_ok, ?_⟩, fuse_all⟩, ?_⟩, pairChain⟩
  · exact classTreeOK_of_K C21113.cg_size C21113.cg_eq (by rw [ku.2, u0_eq]) ku.1
  · rw [t0_eq]
    exact memQ_one (beqT t0Q)

#kc_forall_tree vAll (fun b => CertificateChecks.KernelS63.PD.ch4237V b = true) 64
  CertificateChecks.KernelS63.PD.ch4237V
#kc_forall_tree cAll (fun b => CertificateChecks.KernelS63.PD.ch4237C b = true) 64
  CertificateChecks.KernelS63.PD.ch4237C
#kc_forall_tree qAll (fun b => CertificateChecks.KernelS63.PD.ch4237Q b = true) 8
  CertificateChecks.KernelS63.PD.ch4237Q

theorem invT : invOK' HD.TP TI 4096 = true :=
  MatL.allN_iff.2 fun i hi => I21111.blocks (f := tiK) (n := 64) (m := 64) (fun b hb => vAll b hb)
    (by norm_num) i (by omega)

theorem tq_all : ∀ i < 4096, tqK i = true :=
  fun i hi => I21111.blocks (f := tqK) (n := 64) (m := 64) (fun b hb => cAll b hb) (by norm_num) i
    (by omega)

theorem q_all : ∀ i < 512, qK i = true :=
  fun i hi => I21111.blocks (f := qK) (n := 64) (m := 8) (fun b hb => qAll b hb) (by norm_num) i
    (by omega)

theorem qparts {i : ℕ} (hi : i < 512) :
    allN 8 (fun k => bIf(cmP (AD.QP i) (AD.QG k), true,
      eqM (mw (AD.QP i) (AD.QG k)) (mw (ID.ZP 0) (mw (AD.QG k) (AD.QP i))))) = true ∧
    bIf(eqM (mw (AD.QP i) (AD.QP i)) idP, true, eqM (mw (AD.QP i) (AD.QP i)) (ID.ZP 0)) = true ∧
    bIf(allN 8 fun k => cmP (AD.QP i) (AD.QG k),
      bIf(eqM (AD.QP i) idP, true, eqM (AD.QP i) (ID.ZP 0)), true) = true ∧
    bIf(PD.invK (AD.QP i), bIf(Nat.beq (memS ID.ZP ID.ZS 819 (AD.QP i)) 1, true,
      (List.range 4).any fun k => !eqM (sqU k (AD.QP i)) idP && !eqM (sqU k (AD.QP i)) (ID.ZP 0)),
      true) = true := by
  have h := q_all i hi
  unfold qK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem or2 (a b : Bool) : bIf(a, true, b) = (a || b) := by cases a <;> rfl

theorem all_allN {n : ℕ} {f g : ℕ → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).all f = allN n g := by
  rw [Bool.eq_iff_iff, List.all_eq_true, MatL.allN_iff]
  constructor
  · intro hf k hk
    rw [← h k hk]
    exact hf k (List.mem_range.2 hk)
  · intro hg k hk
    have hk' := List.mem_range.1 hk
    rw [h k hk']
    exact hg k hk'

theorem any_congr' {n : ℕ} {f g : ℕ → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).any f = (List.range n).any g := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨k, hk, e⟩
    exact ⟨k, hk, (h k (List.mem_range.1 hk)) ▸ e⟩
  · rintro ⟨k, hk, e⟩
    exact ⟨k, hk, (h k (List.mem_range.1 hk)).symm ▸ e⟩

theorem memT_one {Y : ℕ} (h : memS HD.TP HD.TS 4096 Y = 1) :
    memR DT.El DT.idx (unpackR 24 Y) = true := by
  obtain ⟨w, hw, he⟩ := memT_of_one h
  rw [dt_mem]
  exact List.any_eq_true.2 ⟨w, List.mem_range.2 hw, by rw [he]; exact eqM_self _⟩

theorem q_el' {i : ℕ} (hi : i < 512) : A21112.DQ.El[i]! = unpackR 24 (AD.QP i) := A21112.q_el hi

theorem qCheck0 : (allLt A21112.DQ.El.size fun i => (List.range qGens.size).all fun k =>
      mulR A21112.DQ.El[i]! qGens[k]! == mulR qGens[k]! A21112.DQ.El[i]! ||
        mulR A21112.DQ.El[i]! qGens[k]! == mulR z0R (mulR qGens[k]! A21112.DQ.El[i]!)) = true := by
  refine allLt_iff.2 fun i hi => ?_
  rw [dq_size] at hi
  rw [A21112.qg_size, all_allN (g := fun k => bIf(cmP (AD.QP i) (AD.QG k), true,
      eqM (mw (AD.QP i) (AD.QG k)) (mw (ID.ZP 0) (mw (AD.QG k) (AD.QP i)))))]
  · exact (qparts hi).1
  · intro k hk
    rw [q_el' hi, A21112.qg_eq k hk, L4234.z0_eq]
    simp only [mulR_unpackR, beq_eq, or2]
    rfl

theorem qCheck1 : (allLt A21112.DQ.El.size fun i =>
    mulR A21112.DQ.El[i]! A21112.DQ.El[i]! == oneR ||
      mulR A21112.DQ.El[i]! A21112.DQ.El[i]! == z0R) = true := by
  refine allLt_iff.2 fun i hi => ?_
  rw [dq_size] at hi
  rw [q_el' hi, L4234.z0_eq, oneR_eq, mulR_unpackR, beq_eq, beq_eq, ← or2]
  exact (qparts hi).2.1

theorem qCheck2 : (allLt A21112.DQ.El.size fun i =>
    !((List.range qGens.size).all fun k => locComm A21112.DQ.El[i]! qGens[k]!) ||
      A21112.DQ.El[i]! == oneR || A21112.DQ.El[i]! == z0R) = true := by
  refine allLt_iff.2 fun i hi => ?_
  rw [dq_size] at hi
  have h := (qparts hi).2.2.1
  rw [A21112.qg_size, all_allN (g := fun k => cmP (AD.QP i) (AD.QG k)) fun k hk => by
    rw [q_el' hi, A21112.qg_eq k hk, comm_eq]]
  rw [q_el' hi, L4234.z0_eq, oneR_eq, beq_eq, beq_eq]
  rw [bIf_eq] at h
  split at h
  · rename_i ha
    rw [ha, ← or2]
    exact h
  · rename_i ha
    simp only [Bool.not_eq_true] at ha
    rw [ha]
    rfl

theorem qCheck3 : (List.range qGens.size).all (fun k => memR DT.El DT.idx qGens[k]!) = true := by
  refine List.all_eq_true.2 fun k hk => ?_
  have hk' : k < 8 := by
    have := List.mem_range.1 hk
    rwa [A21112.qg_size] at this
  rw [A21112.qg_eq k hk', unpackR_mod]
  exact memT_one (beqT (MatL.allN_iff.1 qinT k hk'))

theorem qCheck4 : (allLt DT.El.size fun i => (List.range uGens.size).all fun k =>
    memR A21112.DQ.El A21112.DQ.idx
      (mulR (mulR DT.El[i]! uGens[k]!) (mulR DT.El[DT.inv[i]!]! uGens[k]!))) = true := by
  refine allLt_iff.2 fun i hi => ?_
  rw [dt_size] at hi
  obtain ⟨e1, e2, -⟩ := inv_of_K H4240.ug_size H4240.ug_eq HD.repT invT hi
  have h := tq_all i hi
  unfold tqK at h
  refine List.all_eq_true.2 fun k hk => ?_
  have hk' : k < 4 := by
    have := List.mem_range.1 hk
    rwa [H4240.ug_size] at this
  change memR A21112.DQ.El A21112.DQ.idx
    (mulR (mulR DT.El[i]! uGens[k]!) (mulR DT.El[(DkG HD.TP HD.TPar HD.TLab 4096).inv[i]!]!
      uGens[k]!)) = true
  rw [e1, dt_el hi, dt_el e2, H4240.ug_eq k hk', mulR_unpackR, mulR_unpackR, mulR_unpackR,
    unpackR_mod]
  exact memQ_one (beqT (MatL.allN_iff.1 h k hk'))

theorem qCheck5 : (allLt A21112.DQ.El.size fun i =>
    !(locIsInv A21112.DQ.El[i]!) || memR CZ.T CZ.idx A21112.DQ.El[i]! ||
      (List.range uGens.size).any fun k =>
        let s := mulR (mulR uGens[k]! A21112.DQ.El[i]!) (mulR uGens[k]! A21112.DQ.El[i]!)
        !(s == oneR) && !(s == z0R)) = true := by
  refine allLt_iff.2 fun i hi => ?_
  rw [dq_size] at hi
  have h := (qparts hi).2.2.2
  rw [H4240.ug_size, any_congr' (g := fun k => !eqM (sqU k (AD.QP i)) idP &&
      !eqM (sqU k (AD.QP i)) (ID.ZP 0)) fun k hk => by
    rw [q_el' hi, H4240.ug_eq k hk, L4234.z0_eq, oneR_eq]
    simp only [mulR_unpackR, beq_eq]
    rfl]
  rw [q_el' hi, isInv_eq]
  rw [bIf_eq] at h
  split at h
  · rename_i hv
    rw [hv, Bool.not_true, Bool.false_or]
    rw [bIf_eq] at h
    split at h
    · rename_i hm
      rw [cz_mem_one (beqT hm), Bool.true_or]
    · rw [h, Bool.or_true]
  · rename_i hv
    simp only [Bool.not_eq_true] at hv
    rw [hv]
    rfl

theorem forIn_list_first {α : Type} {k : ℕ} {r : α}
    {f : ℕ → Option α × Unit → Id (ForInStep (Option α × Unit))}
    (hkr : f k (none, ()) = ForInStep.done (some r, ())) :
    ∀ m a, a ≤ k → k < a + m → (∀ i, a ≤ i → i < k → f i (none, ()) = ForInStep.yield (none, ())) →
      forIn (m := Id) (List.range' a m) (none, ()) f = (some r, ()) := by
  intro m
  induction m with
  | zero => intro a _ h _; omega
  | succ m ih =>
    intro a h1 h2 hp
    rw [List.range'_succ, List.forIn_cons]
    by_cases e : a = k
    · subst e
      rw [hkr]
      rfl
    · rw [hp a le_rfl (by omega)]
      exact ih (a + 1) (by omega) (by omega) fun i hi1 hi2 => hp i (by omega) hi2

theorem forIn_list_none {α : Type} {f : ℕ → Option α × Unit → Id (ForInStep (Option α × Unit))} :
    ∀ m a, (∀ i, a ≤ i → i < a + m → f i (none, ()) = ForInStep.yield (none, ())) →
      forIn (m := Id) (List.range' a m) (none, ()) f = (none, ()) := by
  intro m
  induction m with
  | zero => intro a _; rfl
  | succ m ih =>
    intro a hp
    rw [List.range'_succ, List.forIn_cons, hp a le_rfl (by omega)]
    exact ih (a + 1) fun i hi1 hi2 => hp i (by omega) (by omega)

theorem range_list {β : Type} (n : ℕ) (b : β) (f : ℕ → β → Id (ForInStep β)) :
    forIn (m := Id) [:n] b f = forIn (m := Id) (List.range' 0 n) b f := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]

theorem forIn_first {α : Type} {n k : ℕ} {r : α}
    {f : ℕ → Option α × Unit → Id (ForInStep (Option α × Unit))}
    (hp : ∀ i < k, f i (none, ()) = ForInStep.yield (none, ())) (hk : k < n)
    (hkr : f k (none, ()) = ForInStep.done (some r, ())) :
    forIn (m := Id) [:n] (none, ()) f = (some r, ()) := by
  rw [range_list]
  exact forIn_list_first hkr n 0 (Nat.zero_le _) (by omega) fun i _ hi => hp i hi

theorem forIn_none {α : Type} {n : ℕ} {f : ℕ → Option α × Unit → Id (ForInStep (Option α × Unit))}
    (hp : ∀ i < n, f i (none, ()) = ForInStep.yield (none, ())) :
    forIn (m := Id) [:n] (none, ()) f = (none, ()) := by
  rw [range_list]
  exact forIn_list_none n 0 fun i _ hi => hp i (by omega)

theorem pw_parts : Nat.blt pwV 512 = true ∧ Nat.blt pwA 512 = true ∧ Nat.blt pwB 512 = true ∧
    allN pwV (fun iv => bIf(PD.invK (AD.QP iv), Nat.beq (memS ID.ZP ID.ZS 819 (AD.QP iv)) 1,
      true)) = true ∧ pwI pwV = true ∧
    allN pwA (fun ia => bIf(cmP (AD.QP ia) (AD.QP pwV),
      allN 512 fun ib => bIf(pwT ia ib, false, true), true)) = true ∧
    cmP (AD.QP pwA) (AD.QP pwV) = true ∧ allN pwB (fun ib => bIf(pwT pwA ib, false, true)) = true ∧
    pwT pwA pwB = true := by
  have h := pw
  unfold pwK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem qp_lt : ∀ i < 512, AD.QP i < 2 ^ 576 := H4240.q_lt

theorem test_eq {ia ib : ℕ} (ha : ia < 512) (hb : ib < 512) (hv : pwV < 512) :
    (locComm A21112.DQ.El[ib]! A21112.DQ.El[pwV]! &&
      mulR A21112.DQ.El[ia]! A21112.DQ.El[ib]! ==
        mulR z0R (mulR A21112.DQ.El[ib]! A21112.DQ.El[ia]!)) = pwT ia ib := by
  rw [q_el' ha, q_el' hb, q_el' hv, comm_eq, L4234.z0_eq, mulR_unpackR, mulR_unpackR,
    mulR_unpackR, beq_eq, pwT, bAnd_eq']
  rfl

theorem cond_eq {iv : ℕ} (hi : iv < 512) :
    (locIsInv A21112.DQ.El[iv]! && !memR CZ.T CZ.idx A21112.DQ.El[iv]!) =
      (PD.invK (AD.QP iv) && !memR CZ.T CZ.idx (unpackR 24 (AD.QP iv))) := by
  rw [q_el' hi, isInv_eq]

theorem pw_eq : locPairWit CZ A21112.DQ = (pwV, pwA, pwB) := by
  obtain ⟨b1, b2, b3, p4, p5, p6, p7, p8, p9⟩ := pw_parts
  have hv : pwV < 512 := Nat.blt_eq.mp b1
  have ha : pwA < 512 := Nat.blt_eq.mp b2
  have hb : pwB < 512 := Nat.blt_eq.mp b3
  unfold locPairWit
  rw [dq_size]
  rw [forIn_first (k := pwV) (r := (pwV, pwA, pwB)) ?_ hv ?_]
  · rfl
  · intro i hi
    have h := MatL.allN_iff.1 p4 i hi
    try dsimp only
    rw [cond_eq (by omega)]
    rw [bIf_eq] at h
    split at h
    · rename_i hi'
      rw [hi', cz_mem_one (beqT h)]
      rfl
    · rename_i hi'
      simp only [Bool.not_eq_true] at hi'
      rw [hi']
      rfl
  · try dsimp only
    have hc : (locIsInv A21112.DQ.El[pwV]! && !memR CZ.T CZ.idx A21112.DQ.El[pwV]!) = true := by
      unfold pwI at p5
      rw [bAnd_eq', Bool.and_eq_true] at p5
      rw [cond_eq hv, p5.1, cz_mem_zero (qp_lt _ hv) (beqT p5.2)]
      rfl
    rw [if_pos hc]
    rw [forIn_first (k := pwA) (r := (pwV, pwA, pwB)) ?_ ha ?_]
    · rfl
    · intro i hi
      have h := MatL.allN_iff.1 p6 i hi
      try dsimp only
      rw [bIf_eq] at h
      have hi5 : i < 512 := by omega
      split at h
      · rename_i hcm
        have hcm' : locComm A21112.DQ.El[i]! A21112.DQ.El[pwV]! = true := by
          rw [q_el' hi5, q_el' hv, comm_eq]
          exact hcm
        rw [if_pos hcm', forIn_none]
        · rfl
        · intro j hj
          try dsimp only
          have hj' := MatL.allN_iff.1 h j hj
          rw [bIf_eq] at hj'
          split at hj'
          · exact absurd hj' Bool.false_ne_true
          · rename_i ht
            simp only [Bool.not_eq_true] at ht
            rw [test_eq hi5 hj hv, ht]
            rfl
      · rename_i hcm
        have hcm' : locComm A21112.DQ.El[i]! A21112.DQ.El[pwV]! = false := by
          rw [q_el' hi5, q_el' hv, comm_eq]
          simpa using hcm
        rw [hcm']
        rfl
    · try dsimp only
      have hcm' : locComm A21112.DQ.El[pwA]! A21112.DQ.El[pwV]! = true := by
        rw [q_el' ha, q_el' hv, comm_eq]
        exact p7
      rw [if_pos hcm']
      rw [forIn_first (k := pwB) (r := (pwV, pwA, pwB)) ?_ hb ?_]
      · rfl
      · intro j hj
        try dsimp only
        have hj' := MatL.allN_iff.1 p8 j hj
        rw [bIf_eq] at hj'
        split at hj'
        · exact absurd hj' Bool.false_ne_true
        · rename_i ht
          simp only [Bool.not_eq_true] at ht
          rw [test_eq ha (by omega) hv, ht]
          rfl
      · try dsimp only
        rw [test_eq ha hb hv, p9]
        rfl

theorem qCheck6 : locPairWitOK CZ A21112.DQ (locPairWit CZ A21112.DQ) = true := by
  obtain ⟨b1, b2, b3, -, p5, -, p7, -, p9⟩ := pw_parts
  have hv : pwV < 512 := Nat.blt_eq.mp b1
  have ha : pwA < 512 := Nat.blt_eq.mp b2
  have hb : pwB < 512 := Nat.blt_eq.mp b3
  rw [pw_eq]
  unfold locPairWitOK pwI at *
  rw [bAnd_eq', Bool.and_eq_true] at p5
  unfold pwT at p9
  rw [bAnd_eq', Bool.and_eq_true] at p9
  simp only [Bool.and_eq_true, decide_eq_true_eq, dq_size]
  refine ⟨⟨⟨⟨⟨⟨⟨hv, ha⟩, hb⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [q_el' hv, isInv_eq]
    exact p5.1
  · rw [q_el' hv, cz_mem_zero (qp_lt _ hv) (beqT p5.2)]
    rfl
  · rw [q_el' ha, q_el' hv, comm_eq]
    exact p7
  · rw [q_el' hb, q_el' hv, comm_eq]
    exact p9.1
  · rw [q_el' ha, q_el' hb, L4234.z0_eq, mulR_unpackR, mulR_unpackR, mulR_unpackR, beq_eq]
    exact p9.2

theorem qCheck : locQCheck CZ DT A21112.DQ = true := by
  unfold locQCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨A21112.gens_q, ok_of_K A21112.qg_size A21112.qg_eq AD.repQ AD.closQ⟩,
    invOK_of_K H4240.ug_size H4240.ug_eq HD.repT invT⟩, qCheck0⟩, qCheck1⟩, qCheck2⟩, qCheck3⟩,
    qCheck4⟩, qCheck5⟩, qCheck6⟩

theorem cz_ok : CZ.ok d4Gens z0R 819 = true := by
  unfold ClassData.ok
  rw [Bool.and_eq_true]
  refine ⟨classTreeOK_of_K ID.gens_size ID.gens_eq L4234.z0_eq L4234.hK, ?_⟩
  simp [CZ, CkG, ElG]

open Certificates in
theorem c4237 : CFSG.D4Hex.locCheck = true := by
  have e1 : locCz = CZ := by
    unfold locCz
    exact L4234.cz_eq
  have e3 : locEC = C21113.Dk := by
    unfold locEC
    exact C21113.mkEnum_eq
  have e5 : locCzC = CkG ZCP ZCPar ZCLab 3 := by
    unfold locCzC
    exact czC_eq
  have e6 : locCu = CkG UCP UCPar UCLab 24 := by
    unfold locCu
    exact cu_eq
  unfold locCheck
  rw [e1, H4240.et_eq, e3, H4240.eq_eq, e5, e6]
  unfold locCheckOn
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨cz_ok, steps_ok⟩, tCheck⟩, vCheck⟩, fusion⟩, qCheck⟩

end CertificateChecks.KernelS63.P4237

end
