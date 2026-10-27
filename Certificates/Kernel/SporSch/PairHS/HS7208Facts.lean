module

public import Certificates.Kernel.SporSch.PairHS.HS7208E
public import Certificates.Kernel.SporSch.PairHS.HS7208P
public import Certificates.Kernel.SporSch.PairHS.HS2272Facts
public import CFSG.Certificates.Kernel.SporSch.HS7208Sound
public import CFSG.Sporadic.SmallOddCore.HSLocal

public section

set_option maxRecDepth 4000

namespace CertificateChecks.KernelSporSch.HS78

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.HS2272 CFSG.KS.HS7208
open CFSG.KD.LQT.C4126 CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore Subgroup
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HS72

theorem eRun_spec : ∀ (ws : List (List Nat)) (i₀ : Nat) (cs : List (List Nat)),
    eRun i₀ ws cs = true → ∀ k < ws.length, eAt (i₀ + k) (ws.getD k []) (cs.getD k []) = true
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | w :: ws, i₀, cs, h, k, hk => by
    have h' : Bool.rec (motive := fun _ => Bool) false (eRun (Nat.succ i₀) ws cs.tail)
        (eAt i₀ w (cs.headD [])) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases k with _ | k
    · cases cs <;> simpa using h1
    · have := eRun_spec ws (i₀ + 1) cs.tail h2 k (by simpa using hk)
      cases cs <;> simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem tRun_spec : ∀ (ts : List (List Nat)) (j : Nat), tRun ts j = true →
    ∀ k < ts.length, tAt (j + k) (ts.getD k []) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | t :: ts, j, h, k, hk => by
    have h' : Bool.rec (motive := fun _ => Bool) false (tRun ts (Nat.succ j)) (tAt j t) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases k with _ | k
    · simpa using h1
    · have := tRun_spec ts (j + 1) h2 k (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem pRow_spec {b : Nat → Nat} {ib a P : Nat} : ∀ (cs : List (List Nat)) (a' : Nat),
    pRow b ib a P cs a' = true → ∀ k < cs.length,
      pE b ib a (a' + k) (cw (cs.getD k [])) (pg (nat_lit 14) (mask (nat_lit 14)) P (a' + k)) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | c :: cs, a', h, k, hk => by
    have h' : Bool.rec (motive := fun _ => Bool) false (pRow b ib a P cs (Nat.succ a'))
        (pE b ib a a' (cw c) (pg (nat_lit 14) (mask (nat_lit 14)) P a')) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases k with _ | k
    · simpa using h1
    · have := pRow_spec cs (a' + 1) h2 k (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem sm_parts : H78D.w.length = 2880 ∧ H78D.cj.length = 2880 ∧ H78D.xw.length = 72 ∧
    H78D.pv.length = 72 ∧ H78D.sk.length = 4 ∧ (HSD.uc.getD 1 (0, [])).1 = 1 := by
  have h := small_ok
  unfold smallB at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

theorem e_at {i : Nat} (hi : i < 2880) :
    eAt i (H78D.w.getD i []) (H78D.cj.getD i []) = true := by
  have h := eB_all (i / 360) (by change i / 360 < 8; omega) ((i / 45) % 8)
    (Nat.mod_lt _ (by norm_num))
  unfold eB at h
  rw [strictB_val] at h
  have hi0 : Nat.mul (Nat.add (Nat.mul (i / 360) 8) ((i / 45) % 8)) 45 + i % 45 = i := by
    change ((i / 360) * 8 + (i / 45) % 8) * 45 + i % 45 = i
    omega
  have hl := sm_parts
  have := eRun_spec _ _ _ h (i % 45) (by
    rw [List.length_take, List.length_drop, hl.1]
    change i % 45 < min 45 (2880 - ((i / 360) * 8 + (i / 45) % 8) * 45)
    omega)
  rw [hi0] at this
  have e1 : ((H78D.w.drop (Nat.mul (Nat.add (Nat.mul (i / 360) 8) ((i / 45) % 8)) 45)).take
      45).getD (i % 45) [] = H78D.w.getD i [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (Nat.mod_lt _ (by norm_num)),
      List.getElem?_drop, hi0, ← List.getD_eq_getElem?_getD]
  have e2 : ((H78D.cj.drop (Nat.mul (Nat.add (Nat.mul (i / 360) 8) ((i / 45) % 8)) 45)).take
      45).getD (i % 45) [] = H78D.cj.getD i [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (Nat.mod_lt _ (by norm_num)),
      List.getElem?_drop, hi0, ← List.getD_eq_getElem?_getD]
  rwa [e1, e2] at this

theorem p_at {a : Nat} (ha : a < 72) : pAt a = true := by
  have h := pB_all (a / 9) (by change a / 9 < 8; omega) (a % 9) (Nat.mod_lt _ (by norm_num))
  unfold pB at h
  have e : Nat.add (Nat.mul (a / 9) 9) (a % 9) = a := by
    change a / 9 * 9 + a % 9 = a
    omega
  rwa [e] at h

section HS


abbrev Perm3850 : Type := Equiv.Perm (Fin 3850)

noncomputable def xC (i : Nat) : Perm3850 := wordVal (gC 1) (H78D.w.getD i [])

noncomputable def gT (l : Nat) : Perm3850 := wordVal (gC 1) (H78D.gw.getD l [])

noncomputable def Tsyl : Subgroup Perm3850 := closure (gT '' {l | l < 4})

noncomputable def eT (j : Nat) : Perm3850 := wordVal gT (H78D.tw.getD j [])

noncomputable def dU : Perm3850 := wordVal gP (HSD.uc.getD 1 (0, [])).2

noncomputable def wOut : Perm3850 := dU * hsU

theorem cw_rep (w : List Nat) : RepF 3850 (cw w) (wordVal (gC 1) w) :=
  wv_rep (fun k => LC_rep 1 k (by norm_num)) w

theorem xC_rep (i : Nat) : RepF 3850 (cw (H78D.w.getD i [])) (xC i) := cw_rep _

theorem gT_rep (l : Nat) : RepF 3850 (GT l) (gT l) := cw_rep _

theorem eT_rep (j : Nat) : RepF 3850 (wv GT (H78D.tw.getD j [])) (eT j) := wv_rep gT_rep _

theorem t0_rep : RepF 3850 t0 hsT2 := by
  have h := tR_rep (ri := 1) (by norm_num)
  rwa [rt_vals.2.1] at h

theorem dU_mem : dU ∈ hsP := wordVal_mem gP_mem _

theorem w0_rep : RepF 3850 w0 wOut := (wv_rep (fun k => LP_rep k) _).comp U_rep

theorem bs4_lt : ∀ b ∈ bs4, b < 3850 := by
  intro b hb
  simp [bs4] at hb
  omega

theorem faithP : BaseFaithful hsP bs4 := by
  rw [P_eq]
  exact hs_baseFaithful

theorem key_eq {f f' : Nat → Nat} {x : Perm3850} (hf : RepF 3850 f x) (hf' : RepF 3850 f' x) :
    k2 f = k2 f' := by
  unfold k2
  refine keyL_congr _ fun b hb => ?_
  have hb' : b < 3850 := by
    simp [b2] at hb
    omega
  rw [hf b hb', hf' b hb']

theorem tP {r : Nat} (hr : r < 2) : T (rt r) ∈ hsP := by
  have h := t_outer (ri := r) (by omega)
  by_contra hc
  have := h.2 hc
  simp at this
  omega

theorem t0_mem : hsT2 ∈ hsP := by
  have h := tP (r := 1) (by norm_num)
  rwa [rt_vals.2.1] at h

theorem t0_C2 : hsT2 ∈ hsC2 := ⟨t0_mem, mem_centralizer_singleton_iff.2 rfl⟩

theorem t0_sq : hsT2 * hsT2 = 1 := by
  have h := t_sq (ri := 1) (by norm_num)
  rwa [rt_vals.2.1] at h

theorem t0_inv : hsT2⁻¹ = hsT2 := inv_eq_of_mul_eq_one_right t0_sq

theorem gc_mem (k : Nat) : gC 1 k ∈ hsC2 := by
  have h := gC_memK (ri := 1) (by norm_num) k
  rwa [rt_vals.2.1] at h

theorem xC_mem (i : Nat) : xC i ∈ hsC2 := wordVal_mem gc_mem _

theorem comm_t0 {y : Perm3850} (hy : y ∈ hsC2) : y * hsT2 = hsT2 * y :=
  mem_centralizer_singleton_iff.1 (mem_inf.1 hy).2

theorem t0_mul_sq {y : Perm3850} (hy : y ∈ hsC2) (h2 : y * y = 1) :
    hsT2 * y * (hsT2 * y) = 1 := by
  calc hsT2 * y * (hsT2 * y) = hsT2 * (y * hsT2) * y := by group
    _ = hsT2 * (hsT2 * y) * y := by rw [comm_t0 hy]
    _ = (hsT2 * hsT2) * (y * y) := by group
    _ = 1 := by rw [t0_sq, h2, one_mul]

theorem t0_mul_ne {y : Perm3850} (hy : y ≠ hsT2) : hsT2 * y ≠ 1 := fun h => by
  apply hy
  rw [eq_inv_of_mul_eq_one_right h, t0_inv]

theorem e_parts {i : Nat} (hi : i < 2880) :
    eK i = k2 (cw (H78D.w.getD i [])) ∧ ordK 2880 eK i = true ∧
      clsB (cw (H78D.w.getD i [])) (H78D.cj.getD i []) (eCl i) = true ∧
      (eTx i < 2880 ∧ k2 (fun p => t0 (cw (H78D.w.getD i []) p)) = eK (eTx i)) ∧
      (eCl i = 1 → eCl (eTx i) = 1 → eXp i < 72 ∧ xS (eXp i) = i) ∧
      (i ∉ H78D.sk → witB (cw (H78D.w.getD i [])) (eWi i) = true) ∧
      witB (fun p => w0 (cw (H78D.w.getD i []) p)) (eWo i) = true := by
  have h := e_at hi
  unfold eAt at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
  obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h6
  obtain ⟨h9, h10⟩ := (bAnd_iff _ _).1 h8
  obtain ⟨h11, h12⟩ := (bAnd_iff _ _).1 h10
  rw [strictB_val] at h7
  obtain ⟨h7a, h7b⟩ := (bAnd_iff _ _).1 h7
  refine ⟨Nat.eq_of_beq_eq_true h1, h3, h5, ⟨Nat.blt_eq.mp h7a, Nat.eq_of_beq_eq_true h7b⟩,
    fun c1 c2 => ?_, fun hn => ?_, h12⟩
  · have h9' := bIf_then h9 ((bAnd_iff _ _).2 ⟨Nat.beq_eq.mpr c1, Nat.beq_eq.mpr c2⟩)
    rw [strictB_val] at h9'
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h9'
    exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩
  · have e : memN i H78D.sk = false := by
      cases e : memN i H78D.sk
      · rfl
      · exact absurd ((memN_iff i _).1 e) hn
    exact bIf_other h11 e

theorem eK_inj : ∀ i < 2880, ∀ j < 2880, eK i = eK j → i = j :=
  ordK_inj fun _ hi => (e_parts hi).2.1

theorem xC_inj {i j : Nat} (hi : i < 2880) (hj : j < 2880) (h : xC i = xC j) : i = j := by
  refine eK_inj i hi j hj ?_
  have hr : RepF 3850 (cw (H78D.w.getD j [])) (xC i) := by
    rw [h]
    exact xC_rep j
  rw [(e_parts hi).1, (e_parts hj).1]
  exact key_eq (xC_rep i) hr

theorem C2_enum : ∀ y ∈ hsC2, ∃ i < 2880, y = xC i := by
  have hsub : xC '' ((Finset.range 2880 : Finset ℕ) : Set ℕ) ⊆ (hsC2 : Set Perm3850) := by
    rintro _ ⟨i, -, rfl⟩
    exact xC_mem i
  have hinj : Set.InjOn xC ((Finset.range 2880 : Finset ℕ) : Set ℕ) := fun i hi j hj h =>
    xC_inj (by simpa using hi) (by simpa using hj) h
  have hc : (hsC2 : Set Perm3850).ncard = 2880 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    exact hs_reps.2.2.2.1
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [hc, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]) (Set.toFinite _)
  intro y hy
  have hy' : y ∈ xC '' ((Finset.range 2880 : Finset ℕ) : Set ℕ) := by
    rw [heq]
    exact hy
  obtain ⟨i, hi, rfl⟩ := hy'
  exact ⟨i, by simpa using hi, rfl⟩

theorem idx_of_key {y : Perm3850} (hy : y ∈ hsC2) {f : Nat → Nat} (hf : RepF 3850 f y) {m : Nat}
    (hm : m < 2880) (hk : k2 f = eK m) : y = xC m := by
  obtain ⟨j, hj, rfl⟩ := C2_enum y hy
  have e : eK j = eK m := by rw [(e_parts hj).1, key_eq (xC_rep j) hf, hk]
  rw [eK_inj j hj m hm e]

theorem eq_of_key {y z : Perm3850} (hy : y ∈ hsC2) (hz : z ∈ hsC2) {f g : Nat → Nat}
    (hf : RepF 3850 f y) (hg : RepF 3850 g z) (hk : k2 f = k2 g) : y = z := by
  obtain ⟨j, hj, rfl⟩ := C2_enum z hz
  exact idx_of_key hy hf hj (hk.trans ((key_eq hg (xC_rep j)).trans (e_parts hj).1.symm))

theorem tx_eq {i : Nat} (hi : i < 2880) : hsT2 * xC i = xC (eTx i) :=
  idx_of_key (mul_mem t0_C2 (xC_mem i)) (t0_rep.comp (xC_rep i)) (e_parts hi).2.2.2.1.1
    (e_parts hi).2.2.2.1.2

theorem cl_lt {i : Nat} (hi : i < 2880) (h2 : xC i * xC i = 1) (h1 : xC i ≠ 1) :
    eCl i < 2 ∧ wordVal gP (H78D.cj.getD i []) * xC i * (wordVal gP (H78D.cj.getD i []))⁻¹ =
      T (rt (eCl i)) := by
  have h := (e_parts hi).2.2.1
  unfold clsB at h
  have hxP : xC i ∈ hsP := (mem_inf.1 (xC_mem i)).1
  have c1 : eqOnL bs4 (fun p => cw (H78D.w.getD i []) (cw (H78D.w.getD i []) p)) (fun p => p) =
      true := eqOnL_of_eq bs4_lt ((xC_rep i).comp (xC_rep i)) (h2 ▸ RepF.one)
  have c2 : neL bs4 (cw (H78D.w.getD i [])) (fun p => p) = true := by
    unfold neL
    cases e : eqOnL bs4 (cw (H78D.w.getD i [])) (fun p => p)
    · rfl
    · exact absurd (eq_of_eqOnL faithP (xC_rep i) RepF.one hxP (one_mem _) e) h1
  have h' := bIf_then h ((bAnd_iff _ _).2 ⟨c1, c2⟩)
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h'
  have hr : eCl i < 2 := Nat.blt_eq.mp h3
  have hd := wordVal_mem gP_mem (H78D.cj.getD i [])
  exact ⟨hr, eq_of_eqOnL faithP (cjv_rep (fun k => LP_rep k) gP_inv (xC_rep i) _)
    (tR_rep (by omega)) (mul_mem (mul_mem hd hxP) (inv_mem hd)) (tP hr) h4⟩

theorem cl_one {i : Nat} (hi : i < 2880) (h2 : xC i * xC i = 1) (h1 : xC i ≠ 1)
    (hg : ∃ g ∈ hsP, xC i = g * hsT2 * g⁻¹) : eCl i = 1 := by
  obtain ⟨hr, he⟩ := cl_lt hi h2 h1
  rcases (by omega : eCl i = 0 ∨ eCl i = 1) with h0 | h0
  · exfalso
    obtain ⟨g, hg, hgx⟩ := hg
    have hd := wordVal_mem gP_mem (H78D.cj.getD i [])
    rw [h0, rt_vals.1, hgx] at he
    have e : T 5 = (wordVal gP (H78D.cj.getD i []) * g) * hsT2 *
        (wordVal gP (H78D.cj.getD i []) * g)⁻¹ := by
      rw [← he]
      group
    have hc1 : Nat.card ↥(hsP ⊓ centralizer ({T 5} : Set Perm3850)) = 7680 := hs_reps.2.2.1
    rw [e, inf_centralizer_conj hsP (hsP.mul_mem hd hg),
      Subgroup.card_map_of_injective (MulAut.conj _).injective] at hc1
    have hc2 : Nat.card ↥(hsP ⊓ centralizer ({hsT2} : Set Perm3850)) = 2880 := hs_reps.2.2.2.1
    omega
  · exact h0

theorem mem_X {y : Perm3850} (hy : y ∈ hsC2) (h2 : y * y = 1) (h1 : y ≠ 1) (ht : y ≠ hsT2)
    (hg : ∃ g ∈ hsP, y = g * hsT2 * g⁻¹) (hg' : ∃ g ∈ hsP, hsT2 * y = g * hsT2 * g⁻¹) :
    ∃ a < 72, y = xC (xS a) := by
  obtain ⟨i, hi, rfl⟩ := C2_enum y hy
  have c1 := cl_one hi h2 h1 hg
  have htx := tx_eq hi
  have hti : eTx i < 2880 := (e_parts hi).2.2.2.1.1
  have c2 : eCl (eTx i) = 1 := by
    refine cl_one hti ?_ ?_ ?_
    · rw [← htx]
      exact t0_mul_sq hy h2
    · rw [← htx]
      exact t0_mul_ne ht
    · rw [← htx]
      exact hg'
  obtain ⟨ha, hx⟩ := (e_parts hi).2.2.2.2.1 c1 c2
  exact ⟨_, ha, by rw [hx]⟩

theorem tb_parts : tRun H78D.tw 0 = true ∧ H78D.tw.length = 64 ∧ H78D.gw.length = 4 ∧
    H78D.j0 < 64 ∧ tK H78D.j0 = k2 t0 := by
  have h := t0_ok
  unfold tB at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.blt_eq.mp h4,
    Nat.eq_of_beq_eq_true h5⟩

theorem tAt_parts {j : Nat} (hj : j < 64) :
    tK j = k2 (wv GT (H78D.tw.getD j [])) ∧ ordK 64 tK j = true ∧
      ∀ l < 4, tM (j * 4 + l) < 64 ∧
        k2 (fun p => wv GT (H78D.tw.getD j []) (GT l p)) = tK (tM (j * 4 + l)) := by
  have h := tRun_spec _ _ tb_parts.1 j (by rw [tb_parts.2.1]; exact hj)
  rw [Nat.zero_add] at h
  unfold tAt at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  refine ⟨Nat.eq_of_beq_eq_true h1, h3, fun l hl => ?_⟩
  have h5 := allN_spec h4 l hl
  rw [strictB_val] at h5
  obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h5
  exact ⟨Nat.blt_eq.mp h6, Nat.eq_of_beq_eq_true h7⟩

theorem gT_mem (l : Nat) : gT l ∈ Tsyl := by
  by_cases hl : l < 4
  · exact subset_closure ⟨l, hl, rfl⟩
  · have e : H78D.gw.getD l [] = [] :=
      List.getD_eq_default _ _ (by rw [tb_parts.2.2.1]; omega)
    rw [gT, e, wordVal_nil]
    exact one_mem _

theorem Tsyl_le : Tsyl ≤ hsC2 := by
  rw [Tsyl, closure_le]
  rintro _ ⟨l, -, rfl⟩
  exact wordVal_mem gc_mem _

theorem eT_mem (j : Nat) : eT j ∈ Tsyl := wordVal_mem gT_mem _

theorem eT_inj {i j : Nat} (hi : i < 64) (hj : j < 64) (h : eT i = eT j) : i = j := by
  refine ordK_inj (fun _ hk => (tAt_parts hk).2.1) i hi j hj ?_
  have hr : RepF 3850 (wv GT (H78D.tw.getD j [])) (eT i) := by
    rw [h]
    exact eT_rep j
  rw [(tAt_parts hi).1, (tAt_parts hj).1]
  exact key_eq (eT_rep i) hr

theorem Tsyl_enum : ∀ x ∈ Tsyl, ∃ j < 64, x = (eT 0)⁻¹ * eT j := by
  refine mem_of_enum (E := fun j => (eT 0)⁻¹ * eT j) ⟨0, by norm_num, inv_mul_cancel _⟩ ?_
  rintro i hi _ ⟨l, hl, rfl⟩
  obtain ⟨hm, hk⟩ := (tAt_parts hi).2.2 l hl
  refine ⟨_, hm, ?_⟩
  have e : eT i * gT l = eT (tM (i * 4 + l)) :=
    eq_of_key (mul_mem (Tsyl_le (eT_mem i)) (Tsyl_le (gT_mem l))) (Tsyl_le (eT_mem _))
      ((eT_rep i).comp (gT_rep l)) (eT_rep _) (hk.trans (tAt_parts hm).1)
  beta_reduce
  rw [mul_assoc, e]

theorem card_Tsyl : Nat.card Tsyl = 64 := by
  have hc : Nat.card Tsyl = (Tsyl : Set Perm3850).ncard := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  apply le_antisymm
  · have hsub : (Tsyl : Set Perm3850) ⊆
        (fun j => (eT 0)⁻¹ * eT j) '' ((Finset.range 64 : Finset ℕ) : Set ℕ) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Tsyl_enum x hx
      exact ⟨j, by simpa using hj, rfl⟩
    calc Nat.card Tsyl = (Tsyl : Set Perm3850).ncard := hc
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ((Finset.range 64 : Finset ℕ) : Set ℕ).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 64 := by rw [Set.ncard_coe_finset, Finset.card_range]
  · have hsub : eT '' ((Finset.range 64 : Finset ℕ) : Set ℕ) ⊆ (Tsyl : Set Perm3850) := by
      rintro _ ⟨j, -, rfl⟩
      exact eT_mem j
    have hinj : Set.InjOn eT ((Finset.range 64 : Finset ℕ) : Set ℕ) := fun i hi j hj h =>
      eT_inj (by simpa using hi) (by simpa using hj) h
    calc 64 = (eT '' ((Finset.range 64 : Finset ℕ) : Set ℕ)).ncard := by
          rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
      _ ≤ (Tsyl : Set Perm3850).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card Tsyl := hc.symm

theorem t0_mem_Tsyl : hsT2 ∈ Tsyl := by
  obtain ⟨-, -, -, hj, hk⟩ := tb_parts
  have e : hsT2 = eT H78D.j0 :=
    eq_of_key t0_C2 (Tsyl_le (eT_mem _)) t0_rep (eT_rep _) (hk.symm.trans (tAt_parts hj).1)
  rw [e]
  exact eT_mem _

theorem wOut_conj : wOut * hsT2 = hsT2 * wOut := by
  obtain ⟨-, -, h1, h2⟩ := data_parts (ri := 1) (by norm_num)
  have hu : RepF 3850 (fun x => uP (tR 1 (uP x))) (hsU * T (rt 1) * hsU) := by
    rw [mul_assoc]
    exact U_rep.comp ((tR_rep (ri := 1) (by norm_num)).comp U_rep)
  have hrep := cjv_rep (fun k => LP_rep k) gP_inv hu (HSD.uc.getD 1 (0, [])).2
  have hd := P_le_R dU_mem
  have heq := eqR hrep (tR_rep h1) (mul_mem (mul_mem hd (mul_mem (mul_mem U_mem_R
    (t_mem (ri := 1) (by norm_num))) U_mem_R)) (inv_mem hd)) (t_mem h1) h2
  have e1 : (HSD.uc.getD 1 (0, [])).1 = 1 := sm_parts.2.2.2.2.2
  rw [e1, rt_vals.2.1] at heq
  have hc : wOut * hsT2 * wOut⁻¹ = hsT2 := by
    calc wOut * hsT2 * wOut⁻¹ = dU * (hsU * hsT2 * hsU⁻¹) * dU⁻¹ := by
          rw [wOut]
          group
      _ = hsT2 := by
          rw [U_inv]
          exact heq
  exact mul_inv_eq_iff_eq_mul.1 hc

theorem wOut_inv_mul {x : Perm3850} (hx : x * hsU ∈ hsP) : wOut⁻¹ * x ∈ hsP := by
  have h := U_conj _ (hsP.mul_mem (hsP.inv_mem dU_mem) hx)
  have e1 : wOut⁻¹ = hsU * dU⁻¹ := by rw [wOut, mul_inv_rev, U_inv]
  have e2 : hsU * (dU⁻¹ * (x * hsU)) * hsU⁻¹ = hsU * dU⁻¹ * x := by group
  rw [e1, ← e2]
  exact h

theorem witB_spec {f : Nat → Nat} {v : Nat} (h : witB f v = true) {x : Perm3850}
    (hf : RepF 3850 f x) : x * gT (v % 4) ≠ gT (v % 4) * x :=
  ncW_spec h hf (gT_rep _)

theorem cent_Tsyl : Nat.card ↥(hsR ⊓ centralizer (Tsyl : Set Perm3850)) ≤ 4 := by
  classical
  have hsub : ((hsR ⊓ centralizer (Tsyl : Set Perm3850) : Subgroup Perm3850) : Set Perm3850) ⊆
      ↑(H78D.sk.map xC).toFinset := by
    intro x hx
    obtain ⟨hxR, hxc⟩ := mem_inf.1 hx
    have hxT : ∀ g ∈ Tsyl, g * x = x * g := fun g hg => mem_centralizer_iff.1 hxc g hg
    have hxt : x * hsT2 = hsT2 * x := (hxT _ t0_mem_Tsyl).symm
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    rcases memR.1 hxR with hxP | hxU
    · obtain ⟨i, hi, rfl⟩ := C2_enum x ⟨hxP, mem_centralizer_singleton_iff.2 hxt⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hn
      exact witB_spec ((e_parts hi).2.2.2.2.2.1 hn) (xC_rep i) (hxT _ (gT_mem _)).symm
    · exfalso
      have hyt : (wOut⁻¹ * x) * hsT2 = hsT2 * (wOut⁻¹ * x) :=
        ((Commute.inv_left (wOut_conj : Commute wOut hsT2)).mul_left (hxt : Commute x hsT2)).eq
      obtain ⟨i, hi, hix⟩ := C2_enum _ ⟨wOut_inv_mul hxU, mem_centralizer_singleton_iff.2 hyt⟩
      have hx : x = wOut * xC i := by
        rw [← hix]
        group
      have := witB_spec (e_parts hi).2.2.2.2.2.2 (w0_rep.comp (xC_rep i))
      rw [← hx] at this
      exact this (hxT _ (gT_mem _)).symm
  calc Nat.card ↥(hsR ⊓ centralizer (Tsyl : Set Perm3850))
      ≤ Nat.card ↥(↑(H78D.sk.map xC).toFinset : Set Perm3850) :=
        Nat.card_mono (Finset.finite_toSet _) hsub
    _ = (H78D.sk.map xC).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (H78D.sk.map xC).length := List.toFinset_card_le _
    _ = 4 := by rw [List.length_map, sm_parts.2.2.2.2.1]

theorem exists_conj_eq_Tsyl {S : Subgroup Perm3850} (hS : S ≤ hsC2) (hc : Nat.card S = 64) :
    ∃ c ∈ hsC2, S.map (MulAut.conj c).toMonoidHom = Tsyl := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : Nat.card hsC2 = 2880 := hs_reps.2.2.2.1
  have hfac : (Nat.card hsC2).factorization 2 = 6 := by
    rw [hC]
    have h1 : 6 ≤ (2880 : ℕ).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).1 (by norm_num)
    have h2 : ¬ 7 ≤ (2880 : ℕ).factorization 2 := fun h7 => by
      have := (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).2 h7
      omega
    omega
  have hcS : Nat.card (S.subgroupOf hsC2) = 2 ^ (Nat.card hsC2).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv, hc, hfac]
    norm_num
  have hcT : Nat.card (Tsyl.subgroupOf hsC2) = 2 ^ (Nat.card hsC2).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tsyl_le).toEquiv, card_Tsyl, hfac]
    norm_num
  obtain ⟨c, hcst⟩ := MulAction.exists_smul_eq (↥hsC2) (Sylow.ofCard _ hcS) (Sylow.ofCard _ hcT)
  refine ⟨c, c.2, ?_⟩
  have key : ∀ y : ↥hsC2, y ∈ Tsyl.subgroupOf hsC2 ↔ c⁻¹ * y * c ∈ S.subgroupOf hsC2 := by
    intro y
    have h1 : y ∈ ((c • Sylow.ofCard _ hcS : Sylow 2 ↥hsC2) : Subgroup ↥hsC2) ↔
        y ∈ Tsyl.subgroupOf hsC2 := by
      rw [hcst, Sylow.coe_ofCard]
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Sylow.coe_ofCard, MulAut.smul_def, MulAut.conj_inv_apply]
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hsC : s ∈ hsC2 := hS hs
    have hy := (key ⟨_, hsC2.mul_mem (hsC2.mul_mem c.2 hsC) (hsC2.inv_mem c.2)⟩).2 (by
      rw [Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using hs)
    rw [Subgroup.mem_subgroupOf] at hy
    simpa [MulAut.conj_apply] using hy
  · intro hx
    have hxC : x ∈ hsC2 := Tsyl_le hx
    have hy := (key ⟨x, hxC⟩).1 (by rw [Subgroup.mem_subgroupOf]; exact hx)
    rw [Subgroup.mem_subgroupOf] at hy
    refine ⟨_, hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem cent_le_four (S : Subgroup Perm3850) (hS : S ≤ hsC2) (hc : Nat.card S = 64) :
    Nat.card ↥(hsR ⊓ centralizer (S : Set Perm3850)) ≤ 4 := by
  obtain ⟨c, hcC, hmap⟩ := exists_conj_eq_Tsyl hS hc
  have hcR : c ∈ hsR := P_le_R (mem_inf.1 hcC).1
  have hmem : ∀ x ∈ hsR ⊓ centralizer (S : Set Perm3850),
      c * x * c⁻¹ ∈ hsR ⊓ centralizer (Tsyl : Set Perm3850) := by
    intro x hx
    obtain ⟨hxR, hxc⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨mul_mem (mul_mem hcR hxR) (inv_mem hcR), ?_⟩
    rw [mem_centralizer_iff]
    intro t ht
    rw [← hmap] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have hsx : s * x = x * s := (mem_centralizer_iff.1 hxc) s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * s * c⁻¹ * (c * x * c⁻¹) = c * (s * x) * c⁻¹ := by group
      _ = c * (x * s) * c⁻¹ := by rw [hsx]
      _ = c * x * c⁻¹ * (c * s * c⁻¹) := by group
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : ↥(hsR ⊓ centralizer (S : Set Perm3850)) =>
      (⟨c * x * c⁻¹, hmem x x.2⟩ : ↥(hsR ⊓ centralizer (Tsyl : Set Perm3850)))) ?_) cent_Tsyl
  intro a b h
  have e := congrArg Subtype.val h
  exact Subtype.ext (mul_left_cancel (mul_right_cancel e))

theorem pAt_parts {a : Nat} (ha : a < 72) :
    xS a < 2880 ∧ k2 (cw (H78D.xw.getD a [])) = eK (xS a) ∧
      pRow (cw (H78D.xw.getD a [])) (xS a) a (H78D.pv.getD a 0) H78D.xw 0 = true := by
  have h := p_at ha
  unfold pAt at h
  rw [strictB_val, strictB_val] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h3, h4⟩

theorem xw_eq {a : Nat} (ha : a < 72) : wordVal (gC 1) (H78D.xw.getD a []) = xC (xS a) :=
  idx_of_key (wordVal_mem gc_mem _) (cw_rep _) (pAt_parts ha).1 (pAt_parts ha).2.1

theorem pE_cases {b c : Nat → Nat} {ib a a' v : Nat} (h : pE b ib a a' c v = true) :
    (a' = a ∨ xS a' = eTx ib) ∨ ncW 3850 b c (v / 2) = true ∨
      ∃ m, m < 2880 ∧ k2 (fun p => b (c p)) = eK m ∧ ¬ (eCl m = 1 ∧ eCl (eTx m) = 1) := by
  unfold pE at h
  cases h0 : Nat.beq v 0
  · have h' := bIf_other h h0
    cases h1 : Nat.beq (Nat.mod v 2) 1
    · have h'' := bIf_other h' h1
      rw [strictB_val] at h''
      obtain ⟨x1, x2⟩ := (bAnd_iff _ _).1 h''
      obtain ⟨x3, x4⟩ := (bAnd_iff _ _).1 x2
      refine Or.inr (Or.inr ⟨_, Nat.blt_eq.mp x1, Nat.eq_of_beq_eq_true x3, fun ⟨e1, e2⟩ => ?_⟩)
      have := bIf_then x4 ((bAnd_iff _ _).2 ⟨Nat.beq_eq.mpr e1, Nat.beq_eq.mpr e2⟩)
      exact Bool.noConfusion this
    · exact Or.inr (Or.inl (bIf_then h' h1))
  · have h' := bIf_then h h0
    cases h2 : Nat.beq a' a
    · exact Or.inl (Or.inr (Nat.eq_of_beq_eq_true (bIf_other h' h2)))
    · exact Or.inl (Or.inl (Nat.eq_of_beq_eq_true h2))

theorem no_pure (b c : Perm3850) (hb : b ∈ hsC2) (hc : c ∈ hsC2) (hbc : b * c = c * b)
    (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hb2 : b * b = 1) (hc2 : c * c = 1) (hbt : b ≠ hsT2)
    (hct : c ≠ hsT2) (hcb : c ≠ b) (hctb : c ≠ hsT2 * b)
    (hx : ∀ x ∈ ({b, c, b * c, hsT2 * b, hsT2 * c, hsT2 * (b * c)} : Set Perm3850),
      ∃ g ∈ hsP, x = g * hsT2 * g⁻¹) : False := by
  obtain ⟨a, ha, hab⟩ := mem_X hb hb2 hb1 hbt (hx b (by simp)) (hx _ (by simp))
  obtain ⟨a', ha', hac⟩ := mem_X hc hc2 hc1 hct (hx c (by simp)) (hx _ (by simp))
  have hBb : wordVal (gC 1) (H78D.xw.getD a []) = b := by rw [xw_eq ha, hab]
  have hCc : wordVal (gC 1) (H78D.xw.getD a' []) = c := by rw [xw_eq ha', hac]
  have hrb : RepF 3850 (cw (H78D.xw.getD a [])) b := hBb ▸ cw_rep _
  have hrc : RepF 3850 (cw (H78D.xw.getD a' [])) c := hCc ▸ cw_rep _
  have hp := pRow_spec _ 0 (pAt_parts ha).2.2 a' (by rw [sm_parts.2.2.1]; exact ha')
  rw [Nat.zero_add] at hp
  rcases pE_cases hp with (e | e) | e | ⟨m, hm, hk, hn⟩
  · subst e
    exact hcb (hac.trans hab.symm)
  · apply hctb
    rw [hac, e, ← tx_eq (pAt_parts ha).1, hab]
  · exact ncW_spec e hrb hrc hbc
  · have hbcC : b * c ∈ hsC2 := mul_mem hb hc
    have hbcm : b * c = xC m := idx_of_key hbcC (hrb.comp hrc) hm hk
    have hsq : b * c * (b * c) = 1 := by
      calc b * c * (b * c) = b * (c * b) * c := by group
        _ = b * (b * c) * c := by rw [hbc]
        _ = (b * b) * (c * c) := by group
        _ = 1 := by rw [hb2, hc2, one_mul]
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hne : b * c ≠ 1 := fun h => hcb (by rw [eq_inv_of_mul_eq_one_right h, hbinv])
    have hnt : b * c ≠ hsT2 := fun h => hctb (by
      have e1 : c = b⁻¹ * hsT2 := by rw [← h]; group
      rw [e1, hbinv, comm_t0 hb])
    apply hn
    refine ⟨cl_one hm (hbcm ▸ hsq) (hbcm ▸ hne) (hbcm ▸ hx _ (by simp)), ?_⟩
    have htm := tx_eq hm
    rw [← hbcm] at htm
    refine cl_one (e_parts hm).2.2.2.1.1 ?_ ?_ ?_
    · rw [← htm]
      exact t0_mul_sq hbcC hsq
    · rw [← htm]
      exact t0_mul_ne hnt
    · rw [← htm]
      exact hx _ (by simp)

theorem facts7208 :
    (∀ S : Subgroup (Equiv.Perm (Fin 3850)), S ≤ hsC2 → Nat.card S = 64 →
        Nat.card ↥(hsR ⊓ centralizer (S : Set (Equiv.Perm (Fin 3850)))) ≤ 4) ∧
    (∀ b c, b ∈ hsC2 → c ∈ hsC2 → b * c = c * b → b ≠ 1 → c ≠ 1 → b * b = 1 → c * c = 1 →
        b ≠ hsT2 → c ≠ hsT2 → c ≠ b → c ≠ hsT2 * b →
        (∀ x ∈ ({b, c, b * c, hsT2 * b, hsT2 * c, hsT2 * (b * c)} : Set (Equiv.Perm (Fin 3850))),
          ∃ g ∈ hsP, x = g * hsT2 * g⁻¹) →
        False) :=
  ⟨cent_le_four, no_pure⟩

end HS

end CertificateChecks.KernelSporSch.HS78

end
