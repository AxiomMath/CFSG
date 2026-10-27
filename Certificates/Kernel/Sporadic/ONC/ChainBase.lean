
module

public import Certificates.Kernel.Sporadic.ONC.GroupBase
public import Certificates.Kernel.Sporadic.ONC.Defs
public import CFSG.Certificates.Kernel.Spor.ONCSound
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Certificates.Kernel.Spor.TabWords
import Certificates.Kernel.Sporadic.ONC.Slp
import Certificates.Kernel.Sporadic.ONC.Let0
import Certificates.Kernel.Sporadic.ONC.Let1
import Certificates.Kernel.Sporadic.ONC.Let2
import Certificates.Kernel.Sporadic.ONC.Let3
import Certificates.Kernel.Sporadic.ONC.Let4
import Certificates.Kernel.Sporadic.ONC.Let5
import Certificates.Kernel.Sporadic.ONC.Let6
import Certificates.Kernel.Sporadic.ONC.Let7
import Certificates.Kernel.Sporadic.ONC.Inv0
import Certificates.Kernel.Sporadic.ONC.Inv1
import Certificates.Kernel.Sporadic.ONC.T0a
import Certificates.Kernel.Sporadic.ONC.T0b
import Certificates.Kernel.Sporadic.ONC.T0c
import Certificates.Kernel.Sporadic.ONC.T0d
import Certificates.Kernel.Sporadic.ONC.T1
import Certificates.Kernel.Sporadic.ONC.Hd
import Certificates.Kernel.Sporadic.ONC.Misc
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackFld
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Bounds.ONBridge

@[expose] public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ONC.letAll CertificateChecks.KernelSpor.ONC.letSl 1595
#kon_join CertificateChecks.KernelSpor.ONC.invAll CertificateChecks.KernelSpor.ONC.invSl 246
#kon_join CertificateChecks.KernelSpor.ONC.tr0All CertificateChecks.KernelSpor.ONC.tr0 246
#kon_join CertificateChecks.KernelSpor.ONC.tr1All CertificateChecks.KernelSpor.ONC.tr1 12
#kon_join CertificateChecks.KernelSpor.ONC.tr2All CertificateChecks.KernelSpor.ONC.tr2 1
#kon_join CertificateChecks.KernelSpor.ONC.hd0All CertificateChecks.KernelSpor.ONC.hd0 246
#kon_join CertificateChecks.KernelSpor.ONC.hd1All CertificateChecks.KernelSpor.ONC.hd1 246
#kon_join CertificateChecks.KernelSpor.ONC.hd2All CertificateChecks.KernelSpor.ONC.hd2 246

namespace CertificateChecks.KernelSpor.ONC

open Matrix CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.ONC
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt)

theorem slice_all {N S : Nat} {P : Nat → Bool} (hS : N ≤ 1000 * S)
    (h : ∀ s < S, allN (nat_lit 1000) (fun d => strictB (Nat.add (Nat.mul s (nat_lit 1000)) d) fun x =>
      bIf(Nat.blt x N, P x, true)) = true) :
    ∀ x < N, P x = true := by
  intro x hx
  have hs := h (x / 1000) (by omega)
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 hs (x % 1000) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq'] at h'
  have e : Nat.add (Nat.mul (x / 1000) 1000) (x % 1000) = x := by
    change x / 1000 * 1000 + x % 1000 = x
    omega
  have hb : Nat.blt x N = true := Nat.blt_eq.mpr hx
  rw [e, hb] at h'
  exact h'

theorem tree_all {n cnt r S : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (hS : cnt ≤ 1000 * S)
    (h : ∀ s < S, tbfsSlK n cnt r L LV PTS POS PAR LAB TI (Nat.mul s (nat_lit 1000)) (nat_lit 1000) = true) :
    ∀ k < cnt, tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  intro k hk
  have hs := h (k / 1000) (by omega)
  unfold tbfsSlK at hs
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 hs (k % 1000) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq'] at h'
  have e : Nat.add (Nat.mul (k / 1000) 1000) (k % 1000) = k := by
    change k / 1000 * 1000 + k % 1000 = k
    omega
  have hb : Nat.blt k cnt = true := Nat.blt_eq.mpr hk
  rw [e, hb] at h'
  exact h'

theorem vecK_wOfK {X : Nat} (hX : PV X) : vecOf (wOfK X) = vecK X := by
  funext r
  have hp : vP X < 2 ^ 256 := lt_trans hX.2.1 (by norm_num)
  have hm : vM X < 2 ^ 256 := lt_trans hX.2.2 (by norm_num)
  rw [vecOf_apply]
  unfold wOfK
  rw [W.toV_ofV hp hm, V.val_eq_bitVal]
  rfl

theorem pv_key {x : Nat} (hx : x < 245520) : PV (key ONW.K x) :=
  pv_of_canon (CertificateChecks.KernelSpor.ON2.canon2 x hx)

theorem P_key {x : Nat} (hx : x < 245520) : P x = vecK (key ONW.K x) := by
  change vecOf (orbitData ()).keys[x]! = _
  rw [CertificateChecks.KernelSpor.ON2.key_get hx, vecK_wOfK (pv_key hx)]

@[expose] noncomputable def matHom : J0 →* Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  (Units.coeHom _).comp J0.subtype

theorem matHom_apply (g : J0) : matHom g = mat0 g := rfl

theorem col_mat {X : Array V} {L : List Nat}
    (hc : ((CFSG.F3.Native.transpose 154 X).map ofV).size = 154 ∧ L.length = 154 ∧
      ∀ j < 154, ((CFSG.F3.Native.transpose 154 X).map ofV)[j]! = wOfK (L.getD j 0))
    (hL : ∀ j < 154, canon (L.getD j 0) = true) (r c : Fin 154) :
    toMat 154 X r c = vecK (L.getD c.val 0) r := by
  have e := congrFun (congrFun (toMat_transpose (d := 154) X) c) r
  rw [Matrix.transpose_apply] at e
  rw [← e, toMat_apply, ← vecK_wOfK (pv_of_canon (hL c.val c.isLt)), ← hc.2.2 c.val c.isLt,
    vecOf_apply, ← toVM_getElem!, toVM_transpose_map_ofV]

theorem colA (r c : Fin 154) : matHom ga0 r c = vecK (ONW.LA.getD c.val 0) r := by
  rw [matHom_apply, mat0_ga, ← toMat_rowsA]
  exact col_mat CertificateChecks.KernelSpor.ON2.hcA
    (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsAK2
      (CertificateChecks.KernelSpor.ON.list_eq ONW.LA ONW.CA
        (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listA2))) r c

theorem colB (r c : Fin 154) : matHom gb0 r c = vecK (ONW.LB.getD c.val 0) r := by
  rw [matHom_apply, mat0_gb, ← toMat_rowsB]
  exact col_mat CertificateChecks.KernelSpor.ON2.hcB
    (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsBK2
      (CertificateChecks.KernelSpor.ON.list_eq ONW.LB ONW.CB
        (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listB2))) r c

@[expose] noncomputable def regs0G (r : ℕ) : J0 := if r = 0 then ga0 else if r = 1 then gb0 * ga0 * gb0 else 1

@[expose] noncomputable def gs0 (j : ℕ) : J0 := runSLPG prog regs0G (sel.toList.getD j 0)

theorem prog_lt : ∀ ins ∈ prog, instrRegsLt 26 ins := by
  have h : prog.all (instrLt 26) = true := by decide
  intro ins hins
  exact CFSG.Sporadic.SmallF2.instrRegsLt_of_instrLt (List.all_eq_true.1 h ins hins)

theorem ML_facts : ∀ j < 4, CFSG.KS.Ord.Canon 3 154 11 (ML j) ∧ omat (ML j) = mat0 (gs0 j) := by
  have hFA : ∀ c < 154, PV (ONW.LA.getD c 0) := fun c hc =>
    pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsAK2
      (CertificateChecks.KernelSpor.ON.list_eq ONW.LA ONW.CA
        (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listA2)) c hc)
  have hFB : ∀ c < 154, PV (ONW.LB.getD c 0) := fun c hc =>
    pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsBK2
      (CertificateChecks.KernelSpor.ON.list_eq ONW.LB ONW.CB
        (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listB2)) c hc)
  have h := slpK_sound matHom slp_ok (by norm_num) prog_lt (by decide) hFA hFB colA colB
  intro j hj
  exact h j (by change j < 4; exact hj)

theorem getElem!_set!' {α : Type} [Inhabited α] (a : Array α) (k r : ℕ) (v : α)
    (hr : r < a.size) : (a.set! k v)[r]! = if k = r then v else a[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds k v) r (by simpa using hr),
    Array.getElem_setIfInBounds hr, getElem!_pos a r hr]

theorem nPts_eq : nPts = 245520 := rfl

theorem invOK_invT {P : Table} {g : J0} (hP : Rep nPts P g) : invOK nPts P (invT nPts P) = true := by
  have heq : invT nPts P = (List.range' 0 nPts).foldl
      (fun p i => p.set! (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate nPts 0) := by
    unfold invT
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  have hget : ∀ i < nPts, (P[i]!).toNat = idx nPts g i := fun i hi => hP i hi
  have hD : ∀ i < nPts, (P[i]!).toNat < nPts := fun i hi => by
    rw [hget i hi]
    exact idx_lt g hi
  have hd : ∀ i < nPts, ∀ j < i, (P[j]!).toNat ≠ (P[i]!).toNat := fun i hi j hj e => by
    rw [hget i hi, hget j (by omega)] at e
    have := congrArg (idx nPts g⁻¹) e
    rw [idx_inv_idx, idx_inv_idx] at this
    omega
  have hl := CFSG.KS.TW.set_loopV (D := fun i => (P[i]!).toNat) (v := fun i => UInt32.ofNat i)
    (v0 := (0 : UInt32)) hD hd
  unfold invOK
  rw [CFSG.KS.TW.allIn_iff]
  intro i hi
  unfold ap
  rw [heq, hl.2 i hi]
  simp only [UInt32.toNat_ofNat', beq_iff_eq]
  exact Nat.mod_eq_of_lt (by rw [nPts_eq] at hi; omega)

theorem slp_rep : ∀ (prog : List Instr) (st : Array Table × Bool) (ρ : ℕ → J0),
    (∀ ins ∈ prog, instrRegsLt st.1.size ins) → (∀ r < st.1.size, Rep nPts st.1[r]! (ρ r)) →
    st.2 = true →
    (prog.foldl (stepT nPts) st).2 = true ∧ (prog.foldl (stepT nPts) st).1.size = st.1.size ∧
      ∀ r < st.1.size, Rep nPts (prog.foldl (stepT nPts) st).1[r]! (runSLPG prog ρ r)
  | [], _, _, _, hR, hok => ⟨hok, rfl, hR⟩
  | ins :: prog, st, ρ, hp, hR, hok => by
    have hins := hp ins List.mem_cons_self
    have hsz : (stepT nPts st ins).1.size = st.1.size := by
      cases ins <;> simp [stepT]
    have hstep : ∀ r < st.1.size, Rep nPts (stepT nPts st ins).1[r]! (stepG ρ ins r) := by
      intro r hr
      cases ins with
      | mu i j k =>
        simp only [stepT, stepG, getElem!_set!' _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [if_pos rfl, if_pos rfl]
          exact Rep.compT (hR i hins.1) (hR j hins.2.1)
        · rw [if_neg hkr, if_neg (Ne.symm hkr)]
          exact hR r hr
      | pwr e i k =>
        simp only [stepT, stepG, getElem!_set!' _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [if_pos rfl, if_pos rfl]
          exact Rep.powT nPts_lt (hR i hins.1) e
        · rw [if_neg hkr, if_neg (Ne.symm hkr)]
          exact hR r hr
      | iv i k =>
        simp only [stepT, stepG, getElem!_set!' _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [if_pos rfl, if_pos rfl]
          exact Rep.inv_of_invOK (hR i hins.1) (invOK_invT (hR i hins.1))
        · rw [if_neg hkr, if_neg (Ne.symm hkr)]
          exact hR r hr
    have hok' : (stepT nPts st ins).2 = true := by
      cases ins with
      | mu i j k => exact hok
      | pwr e i k => exact hok
      | iv i k =>
        simp only [stepT, hok, Bool.true_and]
        exact invOK_invT (hR i hins.1)
    have ih := slp_rep prog (stepT nPts st ins) (stepG ρ ins)
      (fun ins' h' => hsz ▸ hp ins' (List.mem_cons_of_mem _ h')) (fun r hr => hstep r (hsz ▸ hr)) hok'
    rw [List.foldl_cons]
    refine ⟨ih.1, ih.2.1.trans hsz, fun r hr => ?_⟩
    have := ih.2.2 r (hsz.symm ▸ hr)
    simpa only [runSLPG, List.foldl_cons] using this

theorem wordA_eq : wordG genG0 wordA = ga0 := by
  simp [wordG, wordA, genG0]

theorem wordB_eq : wordG genG0 wordB = gb0 * ga0 * gb0 := by
  simp [wordG, wordB, genG0, mul_assoc]

theorem regs_size : (regs0 (orbitData ())).size = 26 := by
  simp [regs0, nregs]

theorem regs_rep : ∀ r < (regs0 (orbitData ())).size, Rep nPts (regs0 (orbitData ()))[r]! (regs0G r) := by
  intro r hr
  rw [regs_size] at hr
  rw [getElem!_pos _ r (by rw [regs_size]; exact hr)]
  simp only [regs0, Array.getElem_ofFn]
  unfold regs0G
  split_ifs
  · rw [← wordA_eq]
    exact Rep.wordT nPts_lt _ fun l _ => rep_genT0 l
  · rw [← wordB_eq]
    exact Rep.wordT nPts_lt _ fun l _ => rep_genT0 l
  · exact Rep.idT nPts_lt

theorem slp_facts : (runSLP nPts prog (regs0 (orbitData ()))).2 = true ∧
    (runSLP nPts prog (regs0 (orbitData ()))).1.size = 26 ∧
    ∀ r < 26, Rep nPts (runSLP nPts prog (regs0 (orbitData ()))).1[r]! (runSLPG prog regs0G r) := by
  have h := slp_rep prog (regs0 (orbitData ()), true) regs0G
    (fun ins hins => by rw [regs_size]; exact prog_lt ins hins) regs_rep rfl
  rw [regs_size] at h
  exact h

noncomputable abbrev lettersT : Array Table :=
  lettersOf nPts sel (runSLP nPts prog (regs0 (orbitData ()))).1

theorem letters_size : lettersT.size = 8 := by
  simp [lettersT, lettersOf, sel]

theorem sel_get {j : ℕ} (hj : j < 4) : sel[j]! = sel.toList.getD j 0 := by
  interval_cases j <;> rfl

theorem sel_lt {j : ℕ} (hj : j < 4) : sel[j]! < 26 := by
  interval_cases j <;> decide

theorem letters_get {l : ℕ} (hl : l < 8) : lettersT[l]! =
    if l % 2 = 0 then (runSLP nPts prog (regs0 (orbitData ()))).1[sel[l / 2]!]!
    else invT nPts (runSLP nPts prog (regs0 (orbitData ()))).1[sel[l / 2]!]! := by
  rw [getElem!_pos _ l (by rw [letters_size]; exact hl)]
  simp only [lettersT, lettersOf, Array.getElem_ofFn]

theorem rep_even {j : ℕ} (hj : j < 4) : Rep nPts lettersT[2 * j]! (gs0 j) := by
  rw [letters_get (by omega), if_pos (by omega), show 2 * j / 2 = j by omega]
  have := slp_facts.2.2 _ (sel_lt hj)
  rwa [sel_get hj] at this ⊢

theorem rep_odd {j : ℕ} (hj : j < 4) : Rep nPts lettersT[2 * j + 1]! (gs0 j)⁻¹ := by
  rw [letters_get (by omega), if_neg (by omega), show (2 * j + 1) / 2 = j by omega]
  have := slp_facts.2.2 _ (sel_lt hj)
  rw [sel_get hj] at this ⊢
  exact Rep.inv_of_invOK this (invOK_invT this)

theorem inv_pt {j x : ℕ} (hj : j < 4) (hx : x < 245520) :
    LJ (2 * j) x < 245520 ∧ LJ (2 * j + 1) x < 245520 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h := slice_all (N := 245520) (S := 246) (by norm_num) (fun s hs => invAll s hs) x hx
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
  simp only [strictB_eq', bAnd_iff', Nat.blt_eq] at h'
  exact ⟨h'.1, h'.2.1, Nat.eq_of_beq_eq_true h'.2.2⟩

theorem batCnt_mod {x : ℕ} (hx : x < 245520) : x % 154 < batCnt 245520 (x / 154) := by
  rw [batCnt_eq]
  split_ifs with h <;> omega

theorem idx_even {j : ℕ} (hj : j < 4) {x : ℕ} (hx : x < 245520) : idx nPts (gs0 j) x = LJ (2 * j) x := by
  have hlt := (inv_pt hj hx).1
  apply (idx_eq_iff0 hx hlt).2
  rw [smul_vec0, P_key hx, P_key hlt, ← (ML_facts j hj).2]
  have hs1 : x / 154 < 1595 := by omega
  have hs2 : x / 154 * 154 < 245520 := by omega
  have := letS_sound (letAll (x / 154) hs1) (fun j hj => (ML_facts j hj).1)
    (fun x hx => pv_key hx) (fun j hj x hx => (inv_pt hj hx).1) (s := x / 154) hs2 hj
    (batCnt_mod hx)
  rwa [show x / 154 * 154 + x % 154 = x by omega] at this

theorem idx_odd {j : ℕ} (hj : j < 4) {x : ℕ} (hx : x < 245520) :
    idx nPts (gs0 j)⁻¹ x = LJ (2 * j + 1) x := by
  have hy : idx nPts (gs0 j)⁻¹ x < 245520 := idx_lt _ hx
  have e : LJ (2 * j) (idx nPts (gs0 j)⁻¹ x) = x := by
    rw [← idx_even hj hy, idx_idx_inv]
  have := (inv_pt hj hy).2.2
  rw [e] at this
  exact this.symm

theorem letters_LJ : lettersT.size = 8 ∧ ∀ l < 8, ∀ x < 245520, ap lettersT[l]! x = LJ l x := by
  refine ⟨letters_size, fun l hl x hx => ?_⟩
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · rw [rep_even (by omega) x hx, idx_even (by omega) hx]
  · rw [rep_odd (by omega) x hx, idx_odd (by omega) hx]

theorem notB_true {b : Bool} (h : Bool.rec (motive := fun _ => Bool) true false b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem misc_parts : (∀ i < 8, hdTop i = true) ∧ TCNT 0 = 245520 ∧ TCNT 1 = 11172 ∧ TCNT 2 = 168 ∧
    TCNT 3 = 1 ∧ TCNT 4 = 5586 ∧ TCNT 5 = 58653 ∧ TCNT 6 = 52136 ∧ TCNT 7 = 6384 ∧
    r32 LF 0 = 0 ∧ siftQ (fun x => tab ONW.A x) = true ∧ siftQ (fun x => tab ONW.B x) = true ∧
    siftQ (fun x => tab ONW2.NEG x) = false ∧ ordQ aQ 2 1 = true ∧ ordQ bQ 19 1 = true ∧
    ordQ (fun x => aQ (bQ x)) 11 1 = true := by
  have h := misc_ok
  unfold miscOK at h
  rw [bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff',
    bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff'] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨CFSG.KS.Raw.Orb.allN_iff.1 h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5,
    Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8,
    Nat.eq_of_beq_eq_true h9, h10, h11, notB_true h12, h13, h14, h15⟩

theorem tcnt_chain : TCNT 0 = 245520 ∧ TCNT 1 = 11172 ∧ TCNT 2 = 168 :=
  ⟨misc_parts.2.1, misc_parts.2.2.1, misc_parts.2.2.2.1⟩

theorem hd_of {i : ℕ} (hi : i < 8) (hz : ∀ z < TN i, hdZ i z = true) :
    tbfsHdK (TN i) (TROOT i) (TCNT i) (TPTS i) (TPOS i) (TPAR i) (TLAB i) = true := by
  have ht := misc_parts.1 i hi
  unfold hdTop at ht
  unfold tbfsHdK
  rw [bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff'] at ht
  rw [bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff', bAnd_iff']
  exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2,
    CFSG.KS.PackFld.allN_of_forall hz⟩

theorem inv_K : invK LJ 245520 8 = true := by
  unfold invK
  apply CFSG.KS.PackFld.allN_of_forall
  intro j hj
  apply CFSG.KS.PackFld.allN_of_forall
  intro x hx
  have h := slice_all (N := 245520) (S := 246) (by norm_num) (fun s hs => invAll s hs) x hx
  exact CFSG.KS.Raw.Orb.allN_iff.1 h j hj

theorem tree_spec {i : ℕ} (hi : i < 3) :
    tbfsHdK 245520 (BJ i) (TCNT i) (TPTS i) (TPOS i) (TPAR i) (TLAB i) = true ∧
      ∀ k < TCNT i, tbfsPtK 245520 (TCNT i) (lvK LJ BJ 8 i).length LJ (lvAt LJ BJ 8 i) (TPTS i)
        (TPOS i) (TPAR i) (TLAB i) (TTI i) k = true := by
  obtain ⟨c0, c1, c2⟩ := tcnt_chain
  interval_cases i
  · exact ⟨hd_of (i := 0) (by norm_num)
      (slice_all (N := TN 0) (S := 246) (by decide) fun s hs => hd0All s hs),
      tree_all (S := 246) (by rw [c0]; norm_num) fun s hs => tr0All s hs⟩
  · exact ⟨hd_of (i := 1) (by norm_num)
      (slice_all (N := TN 1) (S := 246) (by decide) fun s hs => hd1All s hs),
      tree_all (S := 12) (by rw [c1]; norm_num) fun s hs => tr1All s hs⟩
  · exact ⟨hd_of (i := 2) (by norm_num)
      (slice_all (N := TN 2) (S := 246) (by decide) fun s hs => hd2All s hs),
      tree_all (S := 1) (by rw [c2]; norm_num) fun s hs => tr2All s hs⟩

theorem chain_hyp : ChainHyp 245520 8 3 lettersT chainBase chainQ chainQb LJ BJ QL (fun i => i) TCNT
    TPTS TPOS TPAR TLAB TTI where
  letters := letters_LJ
  inv := ⟨rfl, inv_K⟩
  base := ⟨rfl, by decide⟩
  chk := ⟨rfl, by decide, rfl, by decide⟩
  tree := fun i hi => tree_spec hi

theorem permOfT_rep {T : Table} {g : J0} (h : Rep nPts T g) : permOfT nPts T = MulAction.toPerm g := by
  ext x
  rw [permOfT_val (fun y hy => by rw [h y hy]; exact idx_lt g hy) (fun a ha b hb e => by
      rw [h a ha, h b hb] at e
      have := congrArg (idx nPts g⁻¹) e
      rwa [idx_inv_idx, idx_inv_idx] at this) x, h x x.isLt, idx_of_lt g x.isLt]
  rfl

end CertificateChecks.KernelSpor.ONC

end
