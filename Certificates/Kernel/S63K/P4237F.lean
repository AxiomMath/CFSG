module

public import Certificates.Data.D4HexLocCheck
public import Certificates.Kernel.S63K.PChecksT
public import Certificates.Kernel.S63K.PChecksQ
public import Certificates.Kernel.S63K.H4240
public import Certificates.Kernel.S63K.I21111
public import Certificates.Kernel.S63K.L4234
public import Certificates.Kernel.S63K.C21113
public import CFSG.Certificates.Kernel.S63K.LocForestSound
public import CFSG.Certificates.Kernel.S63K.SortSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.P4237

open CFSG.D4Hex CFSG.LargeExtraspecial.S63 CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KS.SporSch.M24
  CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelS63
  CertificateChecks.KernelS63.PD

theorem sB (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bIf_eq (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_eq' (a b : Bool) : bAnd(a, b) = (a && b) := by
  cases a <;> rfl

theorem beqT {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem eqM_self (A : ℕ) : eqM A A = true := Nat.beq_refl _

theorem mod_lt' (A : ℕ) : A % 2 ^ 576 < 2 ^ 576 := Nat.mod_lt _ (by positivity)

theorem comm_eq (A B : ℕ) : locComm (unpackR 24 A) (unpackR 24 B) = cmP A B := by
  unfold locComm cmP eqM mw
  rw [mulR_unpackR, mulR_unpackR, beq_unpackR]

theorem isInv_eq (A : ℕ) : locIsInv (unpackR 24 A) = PD.invK A := by
  unfold locIsInv PD.invK eqM mw
  rw [mulR_unpackR, oneR_eq, beq_unpackR, beq_unpackR]
  cases Nat.beq (CFSG.KC.F2W.mulW 24 A A % 2 ^ 576) (idP % 2 ^ 576) <;>
    cases Nat.beq (A % 2 ^ 576) (idP % 2 ^ 576) <;> rfl

theorem beq_eq (A B : ℕ) : (unpackR 24 A == unpackR 24 B) = eqM A B := beq_unpackR A B

theorem stepW_lt : ∀ j < 12, ∀ k ∈ stepW j, k < 8 := by decide

theorem u0W_lt : ∀ k ∈ locU0Word, k < 8 := by decide

theorem words_parts : (∀ j < 12, SW j = wordK ID.G idM (stepW j) % 2 ^ 576 ∧
      SV j = wordK ID.G idM (stepW j).reverse % 2 ^ 576) ∧
    U0 0 = wordK ID.G idM locU0Word % 2 ^ 576 := by
  have h := words
  unfold wordsK at h
  rw [bAnd_eq', Bool.and_eq_true] at h
  refine ⟨fun j hj => ?_, beqT h.2⟩
  have h1 := MatL.allN_iff.1 h.1 j hj
  rw [bAnd_eq', Bool.and_eq_true] at h1
  exact ⟨beqT h1.1, beqT h1.2⟩

theorem locSteps_size : locSteps.size = 12 := by
  simp [locSteps, locStepWords]

theorem steps_get {j : ℕ} (hj : j < 12) :
    locSteps[j]! = (unpackR 24 (SW j), unpackR 24 (SV j)) := by
  have hj' : j < locStepWords.length := by simp [locStepWords]; omega
  have e : locSteps[j]! = locStepArr (locStepWords[j]'hj') := by
    rw [getElem!_pos locSteps j (by rw [locSteps_size]; exact hj)]
    simp [locSteps]
  have hw : stepW j = (locStepWords[j]'hj').2 := by
    unfold stepW
    rw [List.getD_eq_getElem _ _ hj']
  have hl : ∀ k ∈ (locStepWords[j]'hj').2, k < 8 := hw ▸ stepW_lt j hj
  have hl' : ∀ k ∈ (locStepWords[j]'hj').2.reverse, k < 8 := fun k hk =>
    hl k (List.mem_reverse.1 hk)
  rw [e, locStepArr, I21111.word_eq hl, I21111.word_eq hl', (words_parts.1 j hj).1,
    (words_parts.1 j hj).2, hw, unpackR_mod (wordK _ _ _), unpackR_mod (wordK _ _ (List.reverse _))]

theorem u0_eq : wordR d4Gens locU0Word = unpackR 24 (U0 0) := by
  rw [I21111.word_eq u0W_lt, words_parts.2, ← unpackR_mod]

noncomputable abbrev DT : EnumData := H4240.DT

theorem dt_size : DT.El.size = 4096 := by simp [DT, H4240.DT, DkG, ElG]

theorem dt_el {i : ℕ} (hi : i < 4096) : DT.El[i]! = unpackR 24 (HD.TP i) := elG_get hi

theorem dt_idx {w : ℕ} (hw : w < 4096) : DT.idx (unpackR 24 (HD.TP w)) = w :=
  idx_of_K H4240.ug_size H4240.ug_eq HD.repT hw

theorem dt_mem (Y : ℕ) : memR DT.El DT.idx (unpackR 24 Y) =
    (List.range 4096).any fun w => eqM (HD.TP w) Y :=
  memR_eq H4240.ug_size H4240.ug_eq HD.repT Y

theorem tdist : bfsDistK HD.TP HD.TS 4096 = true := (bfsK_sound HD.repT).2.2.2.2.1

theorem memT_of_zero {Y : ℕ} (hY : Y < 2 ^ 576) (h : memS HD.TP HD.TS 4096 Y = 0) :
    memR DT.El DT.idx (unpackR 24 Y) = false := by
  rw [dt_mem, List.any_eq_false]
  intro w hw
  have hw' := List.mem_range.1 hw
  rw [H4240.eqM_lt (H4240.t_lt w hw') hY]
  simpa [Nat.beq_eq] using memS_zero tdist h w hw'

theorem memT_pt {w : ℕ} (hw : w < 4096) : memR DT.El DT.idx (unpackR 24 (HD.TP w)) = true := by
  rw [dt_mem]
  exact List.any_eq_true.2 ⟨w, List.mem_range.2 hw, eqM_self _⟩

theorem memT_of_one {Y : ℕ} (h : memS HD.TP HD.TS 4096 Y = 1) :
    ∃ w < 4096, HD.TP w = Y := memS_one tdist h

theorem locY_eq {j x : ℕ} (hj : j < 12) (hx : x < 4096) :
    locY DT j x = unpackR 24 (cjS j (HD.TP x)) := by
  unfold locY
  rw [steps_get hj, dt_el hx, conjI, mulR_unpackR, mulR_unpackR, cjS, mw, mw, ← unpackR_mod]

#kc_forall_tree fAll (fun b => CertificateChecks.KernelS63.PD.ch4237F b = true) 15
  CertificateChecks.KernelS63.PD.ch4237F
#kc_forall_tree iAll (fun b => CertificateChecks.KernelS63.PD.ch4237I b = true) 64
  CertificateChecks.KernelS63.PD.ch4237I
#kc_forall_tree zAll (fun b => CertificateChecks.KernelS63.PD.ch4237Z b = true) 64
  CertificateChecks.KernelS63.PD.ch4237Z

theorem fa_all : ∀ h < 495, ∀ j < 12, faK h j = true := by
  intro h hh j hj
  have := I21111.blocks (f := fun h => allN 12 fun j => faK h j) (n := 33) (m := 15)
    (fun b hb => fAll b hb) (by norm_num) h (by omega)
  exact MatL.allN_iff.1 this j hj

theorem in_all : ∀ i < 4096, inK i = true :=
  fun i hi => I21111.blocks (f := inK) (n := 64) (m := 64) (fun b hb => iAll b hb) (by norm_num) i
    (by omega)

theorem ce_all : ∀ i < 4096, ceK i = true :=
  fun i hi => I21111.blocks (f := ceK) (n := 64) (m := 64) (fun b hb => zAll b hb) (by norm_num) i
    (by omega)

theorem fo_lt : ∀ i < 495, FO i < 4096 := fun i hi => Nat.blt_eq.mp (MatL.allN_iff.1 fbound i hi)

theorem fo_inj : ∀ a < 495, ∀ b < 495, FO a = FO b → a = b := (bfsDistK_sound fdist).2

theorem lact : LAct DT FO FW 495 := by
  intro h hh j hj
  rw [locSteps_size] at hj ⊢
  have hf := fa_all h hh j hj
  unfold faK at hf
  rw [sB, bIf_eq] at hf
  rw [locY_eq hj (fo_lt h hh)]
  split at hf
  · rename_i hc
    rw [bAnd_eq', Bool.and_eq_true] at hc
    have hw : FW (12 * h + j) < 495 := Nat.blt_eq.mp hc.1
    left
    rw [← beqT hc.2]
    exact ⟨memT_pt (fo_lt _ hw), dt_idx (fo_lt _ hw)⟩
  · rw [bAnd_eq', Bool.and_eq_true] at hf
    right
    exact ⟨memT_of_zero (mod_lt' _) (beqT hf.2), beqT hf.1⟩

theorem frun' : orbRunK FW FPa FLa locSteps.size (495 + 1) 0 2 = 495 := by
  rw [locSteps_size]
  exact beqT frun

theorem forest : locForest DT [FO 0, FO 1] =
      ((List.range' 2 (495 - 2)).map fun i => (FO i, FO (FPa i), FLa i)) ∧
    LTree DT FO FPa FLa 495 :=
  locForest_of_K (by norm_num) (fun i hi => by rw [dt_size]; exact fo_lt i hi) fo_inj lact frun'

theorem z0_eq' : z0R = unpackR 24 (HD.TP (FO 0)) := by
  have h := froots
  rw [bAnd_eq', Bool.and_eq_true] at h
  rw [beqT h.1, L4234.z0_eq]

theorem t0_eq' : t0R = unpackR 24 (HD.TP (FO 1)) := by
  have h := froots
  rw [bAnd_eq', Bool.and_eq_true] at h
  rw [beqT h.2, C21113.t0_eq, T0r, ← unpackR_mod]

theorem go_of_tree : ∀ m k (seen : List ℕ), k + m = 495 → 2 ≤ k → (∀ i < k, seen.contains (FO i)) →
    locForestGo DT seen ((List.range' k m).map fun i => (FO i, FO (FPa i), FLa i)) = true := by
  intro m
  induction m with
  | zero => intro k seen _ _ _; rfl
  | succ m ih =>
    intro k seen hk h2 hs
    rw [List.range'_succ, List.map_cons]
    obtain ⟨hp, hl, hm, hi⟩ := forest.2 k h2 (by omega)
    unfold locForestGo
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have hk' : FO k < DT.El.size := by
      rw [dt_size]
      exact fo_lt k (by omega)
    refine ⟨⟨⟨⟨hs _ hp, hl⟩, hk'⟩, ?_⟩, ?_⟩
    · unfold memR at hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      rw [← hi]
      exact beq_iff_eq.2 hm.2.symm
    · refine ih (k + 1) _ (by omega) (by omega) fun i hi' => ?_
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
      · rw [List.contains_cons, hs i hi', Bool.or_true]
      · rw [List.contains_cons, beq_self_eq_true, Bool.true_or]

theorem invChain : locInvChain DT = true := by
  have i0 : DT.idx z0R = FO 0 := by rw [z0_eq', dt_idx (fo_lt 0 (by norm_num))]
  have i1 : DT.idx t0R = FO 1 := by rw [t0_eq', dt_idx (fo_lt 1 (by norm_num))]
  unfold locInvChain
  simp only [i0, i1, forest.1, Bool.and_eq_true, decide_eq_true_eq, dt_size, beq_iff_eq]
  refine ⟨⟨⟨⟨fo_lt 0 (by norm_num), ?_⟩, fo_lt 1 (by norm_num)⟩, ?_⟩, ?_, ?_⟩
  · rw [dt_el (fo_lt 0 (by norm_num)), z0_eq']
  · rw [dt_el (fo_lt 1 (by norm_num)), t0_eq']
  · refine go_of_tree _ 2 _ (by norm_num) le_rfl fun i hi => ?_
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp
    · simp
  · refine allLt_iff.2 fun i hi => ?_
    have hk := in_all i hi
    unfold inK at hk
    rw [bIf_eq] at hk
    rw [dt_el hi, isInv_eq]
    split at hk
    · rename_i hv
      rw [hv, Bool.not_true, Bool.false_or]
      rw [bAnd_eq', Bool.and_eq_true] at hk
      have he : FI i < 495 := Nat.blt_eq.mp hk.1
      have hfi : FO (FI i) = i := beqT hk.2
      rw [List.contains_append, List.map_map]
      by_cases e2 : 2 ≤ FI i
      · have hm : i ∈ (List.range' 2 (495 - 2)).map ((·.1) ∘ fun i => (FO i, FO (FPa i), FLa i)) :=
          List.mem_map.2 ⟨FI i, List.mem_range'.2 ⟨FI i - 2, by omega, by omega⟩, hfi⟩
        rw [List.contains_iff_mem.2 hm, Bool.or_true]
      · obtain e | e : FI i = 0 ∨ FI i = 1 := by omega
        · rw [← hfi, e]
          simp
        · rw [← hfi, e]
          simp
    · rename_i hv
      simp only [Bool.not_eq_true] at hv
      rw [hv]
      rfl

theorem gens_u : gensOK uGens = true := by
  have hd := L4234.gensOK_d4
  unfold gensOK at hd ⊢
  rw [allLt_iff] at hd ⊢
  intro k hk
  rw [H4240.ug_size] at hk
  rw [uGens_getElem hk]
  exact hd _ (by rw [ID.gens_size]; exact uIdx_lt hk)

theorem ok_dt : DT.ok uGens 4096 = true := by
  have h := I21111.ok_dt
  unfold EnumData.ok
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact h

theorem vparts : PD.invK (ID.ZP 0) = true ∧ PD.invK T0r = true ∧ PD.invK (ID.ZP 1) = true ∧
    PD.invK (ID.ZP 5) = true ∧ eqM (mw (ID.ZP 0) (ID.ZP 1)) (ID.ZP 5) = true ∧
    eqM (mw (ID.ZP 1) (ID.ZP 0)) (ID.ZP 5) = true ∧ eqM (mw (ID.ZP 0) (ID.ZP 5)) (ID.ZP 1) = true ∧
    eqM (mw (ID.ZP 5) (ID.ZP 0)) (ID.ZP 1) = true ∧ eqM (mw (ID.ZP 1) (ID.ZP 5)) (ID.ZP 0) = true ∧
    eqM (mw (ID.ZP 5) (ID.ZP 1)) (ID.ZP 0) = true ∧ cmP T0r (ID.ZP 0) = true ∧
    cmP T0r (ID.ZP 1) = true ∧ cmP T0r (ID.ZP 5) = true ∧
    allN 4 (fun k => bAnd(inV k (ID.ZP 0), bAnd(inV k (ID.ZP 1), inV k (ID.ZP 5)))) = true ∧
    (List.range 3).any (fun a => eqM (ZCP a) (ID.ZP 1)) = true ∧
    (List.range 3).any (fun a => eqM (ZCP a) (ID.ZP 5)) = true ∧ Nat.blt (VC 0) 3072 = true ∧
    cmP (CD.EP (VC 0)) (ID.ZP 0) = true ∧ cmP (CD.EP (VC 0)) (ID.ZP 1) = true ∧
    cmP (CD.EP (VC 0)) (ID.ZP 5) = true ∧
    strictB (mw (CD.EP (VC 0)) (CD.EP (VC 0))) (fun s =>
      bIf(eqM s (ID.ZP 0), true, bIf(eqM s (ID.ZP 1), true, eqM s (ID.ZP 5)))) = true := by
  have h := v
  unfold vK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem z0_inv : locIsInv z0R = true := by
  rw [L4234.z0_eq, isInv_eq]
  exact vparts.1

theorem t0_inv : locIsInv t0R = true := by
  rw [C21113.t0_eq, unpackR_mod, isInv_eq]
  exact vparts.2.1

theorem tCheck : locTCheck DT = true := by
  unfold locTCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨gens_u, ok_dt⟩, z0_inv⟩, t0_inv⟩, ?_⟩, invChain⟩
  refine allLt_iff.2 fun i hi => ?_
  rw [dt_size] at hi
  have hc := ce_all i hi
  unfold ceK at hc
  rw [bIf_eq] at hc
  rw [dt_el hi, L4234.z0_eq, beq_eq, oneR_eq, beq_eq, H4240.ug_size]
  split at hc
  · rename_i ha
    have e : ((List.range 4).all fun k => locComm (unpackR 24 (HD.TP i)) uGens[k]!) = true := by
      refine List.all_eq_true.2 fun k hk => ?_
      have hk' := List.mem_range.1 hk
      rw [H4240.ug_eq k hk', comm_eq]
      exact MatL.allN_iff.1 ha k hk'
    rw [e, Bool.not_true, Bool.false_or]
    rw [bIf_eq] at hc
    split at hc
    · rename_i h1
      rw [h1, Bool.true_or]
    · rw [hc, Bool.or_true]
  · rename_i ha
    have e : ((List.range 4).all fun k => locComm (unpackR 24 (HD.TP i)) uGens[k]!) = false := by
      rw [Bool.eq_false_iff]
      intro he
      apply ha
      refine MatL.allN_iff.2 fun k hk => ?_
      have := List.all_eq_true.1 he k (List.mem_range.2 hk)
      rwa [H4240.ug_eq k hk, comm_eq] at this
    rw [e]
    rfl

end CertificateChecks.KernelS63.P4237

end
