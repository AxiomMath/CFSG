module

public import Certificates.Kernel.SporSch.PairHS.HS2272Small
public import Certificates.Kernel.SporSch.PairHS.HS2272Bind
public import Certificates.Kernel.SporSch.PairHS.HS2272S
public import Certificates.Kernel.SporSch.PairHS.Check2220
public import Certificates.Kernel.LocalQT.SV.C4126TB
public import CFSG.Certificates.Kernel.SporSch.HS2272Sound
public import CFSG.Certificates.Kernel.SporSch.HS2272Group
public import CFSG.Sporadic.SmallOddCore.Normalizing

public section

set_option maxRecDepth 4000

namespace CertificateChecks.KernelSporSch.HS72

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.HS2272 CFSG.KD.LQT.C4126
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Monster.B.Co2 Subgroup
open CertificateChecks.KernelSporSch

theorem repF_unpack {P : Nat} {g : Equiv.Perm (Fin 3850)} (h : Rep 3850 (unpack 3850 12 P) g) :
    RepF 3850 (fun x => pg 12 (mask 12) P x) g := fun x hx => by
  change pg 12 (mask 12) P x = _
  rw [← Orb.unpack_get hx]
  exact h ⟨x, hx⟩

noncomputable abbrev T (k : Nat) : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl k)

theorem T_eq {k : Nat} (hk : k < 43) : T k = permOfArr 3850 (unpack 3850 12 (HC.F k)) := by
  change permOfArr 3850 (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl k)) = _
  rw [hsCentTbl_eq hk]

theorem T_rep {k : Nat} (hk : k < 43) : RepF 3850 (tv k) (T k) ∧ RepF 3850 (ti k) (T k)⁻¹ := by
  obtain ⟨-, h2⟩ := invEqK_sound (allN_spec hc_perms k hk)
  obtain ⟨r1, r2⟩ := rep_permOfArr h2
  rw [T_eq hk]
  exact ⟨repF_unpack r1, repF_unpack r2⟩

theorem a_rep (i : Nat) (hi : i < 2) :
    RepF 3850 (fun x => pg 12 (mask 12) (PHSC.S i) x) (hsGen i) ∧
      RepF 3850 (fun x => pg 12 (mask 12) (PHSC.SI i) x) (hsGen i)⁻¹ := by
  have e : hsGen i = PHSCheck.g i := by
    change permOfArr 3850 hsStrongArrs[i]! = _
    rw [PHSCheck.arr_eq i (by omega)]
    rfl
  rw [e]
  exact ⟨repF_unpack (PHSCheck.rep_g i (by omega)).1, repF_unpack (PHSCheck.rep_g i (by omega)).2⟩

noncomputable def gP (k : Nat) : Equiv.Perm (Fin 3850) :=
  if k % 4 = 0 then hsGen 0 else if k % 4 = 1 then (hsGen 0)⁻¹ else if k % 4 = 2 then hsGen 1
    else (hsGen 1)⁻¹

theorem nIf_eq (c : Bool) (a b : Nat) : Bool.rec (motive := fun _ => Nat) b a c = if c then a else b := by
  cases c <;> rfl

theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false fun e => by rw [Nat.beq_eq.mpr e] at h; exact Bool.noConfusion h).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem LP_rep (k : Nat) : RepF 3850 (LP k) (gP k) := by
  have hk := Nat.mod_lt k (show 0 < 4 by norm_num)
  have e : LP k = fun x => pg 12 (mask 12) (lp (k % 4)) x := rfl
  rw [e]
  unfold lp gP
  simp only [nIf_eq, beq_dec, decide_eq_true_eq]
  by_cases h0 : k % 4 = 0
  · simp only [h0, if_true]
    exact (a_rep 0 (by norm_num)).1
  by_cases h1 : k % 4 = 1
  · simp only [h1, if_true, show (1 : Nat) ≠ 0 by norm_num, if_false]
    exact (a_rep 0 (by norm_num)).2
  by_cases h2 : k % 4 = 2
  · simp only [h2, if_true, show (2 : Nat) ≠ 0 by norm_num, show (2 : Nat) ≠ 1 by norm_num,
      if_false]
    exact (a_rep 1 (by norm_num)).1
  · simp only [h0, h1, h2, if_false]
    exact (a_rep 1 (by norm_num)).2

theorem gP_inv (k : Nat) : gP (ivL k) = (gP k)⁻¹ := by
  rw [ivL_eq]
  have hk := Nat.mod_lt k (show 0 < 4 by norm_num)
  by_cases h2 : k % 2 = 0
  · rw [if_pos h2]
    have e : (k + 1) % 4 = k % 4 + 1 := by omega
    have h4 : k % 4 = 0 ∨ k % 4 = 2 := by omega
    unfold gP
    rw [e]
    rcases h4 with h | h <;> simp [h]
  · rw [if_neg h2]
    have e : (k - 1) % 4 = k % 4 - 1 := by omega
    have h4 : k % 4 = 1 ∨ k % 4 = 3 := by omega
    unfold gP
    rw [e]
    rcases h4 with h | h <;> simp [h]

theorem gP_mem (k : Nat) : gP k ∈ hsP := by
  have h0 : hsGen 0 ∈ hsP := subset_closure (by simp)
  have h1 : hsGen 1 ∈ hsP := subset_closure (by simp)
  unfold gP
  split_ifs
  · exact h0
  · exact hsP.inv_mem h0
  · exact h1
  · exact hsP.inv_mem h1

theorem gP_two (i : Nat) (hi : i < 2) : gP (Nat.mul i 2) = hsGen i := by
  unfold gP
  interval_cases i <;> simp

section HS


noncomputable abbrev E (F : Nat) : Equiv.Perm (Fin 3850) := PHSCount.E F

theorem P_eq : hsP = hsChain.originalSubgroup := hsP_eq_original

theorem E_rep' {F : Nat} (hF : nfValidK 4 PHSC.LR F = true) : RepF 3850 (nfp F) (E F) :=
  PHSCount.E_rep hF

theorem E_mem' {F : Nat} (hF : nfValidK 4 PHSC.LR F = true) : E F ∈ hsP := by
  rw [P_eq]
  exact PHSCount.E_mem hF

theorem valid_parts : (∀ j < 22, nfValidK 4 PHSC.LR (bndAt j).2.1 = true) ∧
    (∀ i < 2, nfValidK 4 PHSC.LR (uaF i) = true) ∧ nfValidK 4 PHSC.LR HSD.z0 = true := by
  have h := valid
  unfold validB at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h3, h4⟩ := h
  exact ⟨allN_spec h1, allN_spec h3, h4⟩

theorem U_rep : RepF 3850 uP hsU := (T_rep (k := 0) (by norm_num)).1

theorem bnd_eq {j : Nat} (hj : j < 22) (hk : (bndAt j).1 < 43) :
    T (bndAt j).1 = if (bndAt j).2.2 = true then E (bndAt j).2.1 * hsU else E (bndAt j).2.1 := by
  have hF := valid_parts.1 j hj
  have hb : ∀ x < 3850, tv (bndAt j).1 x = bndP j x := by
    intro x hx
    have h := bindB_all j hj (x / 770) (show x / 770 < 5 by omega)
    exact eqBlk_spec h x (by change (x / 770) * 770 ≤ x; omega) (by
      change x < (x / 770) * 770 + 770; omega)
  have hP : RepF 3850 (bndP j) (if (bndAt j).2.2 = true then E (bndAt j).2.1 * hsU
      else E (bndAt j).2.1) := by
    unfold bndP
    cases ho : (bndAt j).2.2
    · exact E_rep' hF
    · exact (E_rep' hF).comp U_rep
  refine RepF.unique ?_ hP
  intro x hx
  rw [← hb x hx]
  exact (T_rep hk).1 x hx

theorem ua_eq {i : Nat} (hi : i < 2) : hsU * hsGen i * hsU = E (uaF i) := by
  have hF := valid_parts.2.1 i hi
  have hb : ∀ x < 3850, uP (LP (Nat.mul i 2) (uP x)) = nfp (uaF i) x := by
    intro x hx
    have h := uaB_all i hi (x / 770) (show x / 770 < 5 by omega)
    exact eqBlk_spec h x (by change (x / 770) * 770 ≤ x; omega) (by
      change x < (x / 770) * 770 + 770; omega)
  have h1 : RepF 3850 (fun x => uP (LP (Nat.mul i 2) (uP x))) (hsU * (gP (Nat.mul i 2) * hsU)) :=
    U_rep.comp ((LP_rep _).comp U_rep)
  rw [gP_two i hi, ← mul_assoc] at h1
  refine RepF.unique ?_ (E_rep' hF)
  intro x hx
  rw [← hb x hx]
  exact h1 x hx

theorem u_parts : (∀ x < 3850, uP (uP x) = x) ∧ uP 0 ≠ 0 ∧
    (∀ b ∈ bs4, nfp HSD.z0 (uP b) = b) ∧ nfp HSD.z0 (uP 5) ≠ 5 := by
  have h := u_ok
  unfold uB at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h3, h5, h6⟩ := h
  refine ⟨fun x hx => eqBlk_spec h1 x (Nat.zero_le x) hx, fun e => ?_,
    (eqOnL_iff _ _ _).1 h5, fun e => ?_⟩
  · rw [show Nat.beq (uP 0) 0 = true from Nat.beq_eq.mpr e] at h3
    exact Bool.noConfusion h3
  · rw [show Nat.beq (nfp HSD.z0 (uP 5)) 5 = true from Nat.beq_eq.mpr e] at h6
    exact Bool.noConfusion h6

theorem U_sq : hsU * hsU = 1 :=
  RepF.unique (U_rep.comp U_rep) (fun x hx => u_parts.1 x hx)

theorem U_inv : hsU⁻¹ = hsU := inv_eq_of_mul_eq_one_right U_sq

theorem U_ne : hsU ≠ 1 := fun h => u_parts.2.1 (by
  have := U_rep 0 (by norm_num)
  rw [this, h]
  rfl)

noncomputable abbrev Z0 : Equiv.Perm (Fin 3850) := E HSD.z0 * hsU

theorem Z0_rep : RepF 3850 (fun x => nfp HSD.z0 (uP x)) Z0 := (E_rep' valid_parts.2.2).comp U_rep

theorem Z0_fix : ∀ x : Fin 3850, (x : Nat) ∈ PairHS.bs → Z0 x = x := by
  intro x hx
  refine Fin.ext ?_
  rw [← Z0_rep x x.2]
  exact u_parts.2.2.1 x hx

theorem Z0_move : Z0 ⟨5, by norm_num⟩ ≠ ⟨5, by norm_num⟩ := fun h => u_parts.2.2.2 (by
  have e := Z0_rep 5 (by norm_num)
  simp only at e
  rw [e, h])

theorem U_notMem : hsU ∉ hsP := by
  intro hU
  have hZ : Z0 ∈ hsP := hsP.mul_mem (E_mem' valid_parts.2.2) hU
  rw [P_eq] at hZ
  exact Z0_move (by rw [hs_baseFaithful Z0 hZ Z0_fix]; rfl)

theorem U_conj : ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP := by
  have hle : hsP ≤ hsP.comap (MulAut.conj hsU).toMonoidHom := by
    unfold hsP
    rw [closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, U_inv]
    rcases hx with rfl | rfl
    · rw [ua_eq (i := 0) (by norm_num)]
      exact E_mem' (valid_parts.2.1 0 (by norm_num))
    · rw [ua_eq (i := 1) (by norm_num)]
      exact E_mem' (valid_parts.2.1 1 (by norm_num))
  intro p hp
  have := hle hp
  simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem U_sq' : hsU ^ 2 = 1 := by rw [sq, U_sq]

theorem memR {x : Equiv.Perm (Fin 3850)} : x ∈ hsR ↔ x ∈ hsP ∨ x * hsU ∈ hsP :=
  mem_sup_zpowers_iff U_sq' U_conj

theorem faithR : BaseFaithful hsR bsR := by
  intro h hR hfix
  have hfix4 : ∀ x : Fin 3850, (x : Nat) ∈ PairHS.bs → h x = x := fun x hx =>
    hfix x (by simp [bsR, PairHS.bs] at hx ⊢; omega)
  rcases memR.1 hR with hP | hPu
  · rw [P_eq] at hP
    exact hs_baseFaithful h hP hfix4
  · exfalso
    have hq : h * Z0⁻¹ ∈ hsP := by
      have e : h * Z0⁻¹ = (h * hsU) * (E HSD.z0)⁻¹ := by
        rw [Z0, mul_inv_rev, U_inv, mul_assoc]
      rw [e]
      exact hsP.mul_mem hPu (hsP.inv_mem (E_mem' valid_parts.2.2))
    rw [P_eq] at hq
    have h1 := hs_baseFaithful _ hq fun x hx => by
      have hzi : Z0⁻¹ x = x := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact (Z0_fix x hx).symm
      rw [Equiv.Perm.mul_apply, hzi]
      exact hfix4 x hx
    have hz : h = Z0 := mul_inv_eq_one.1 h1
    apply Z0_move
    rw [← hz]
    exact hfix ⟨5, by norm_num⟩ (by simp [bsR])

theorem bsR_lt : ∀ b ∈ bsR, b < 3850 := by
  intro b hb
  simp [bsR] at hb
  omega

theorem eqR {f g : Nat → Nat} {x y : Equiv.Perm (Fin 3850)} (hf : RepF 3850 f x)
    (hg : RepF 3850 g y) (hx : x ∈ hsR) (hy : y ∈ hsR) (h : eqOnL bsR f g = true) : x = y :=
  eq_of_eqOnL faithR hf hg hx hy h

theorem P_le_R : hsP ≤ hsR := le_sup_left

theorem U_mem_R : hsU ∈ hsR := mem_sup_right (mem_zpowers hsU)

theorem hs_trans : ∀ x y : Fin 3850, ∃ p ∈ hsP, p x = y := by
  have h0 : 0 < hsChain.baseCount := by rw [hsChain_baseCount]; norm_num
  have hb : hsChain.base.get ⟨0, h0⟩ = 0 := by
    apply Fin.ext
    have := hsChain_base
    have h1 : (hsChain.base.toList.map Fin.val)[0]'(by simp [h0]) = 0 := by simp [this]
    simpa [Vector.get_eq_getElem] using h1
  have htrans := transitive_of_orbitSize hsChain hsChain_valid.1 h0
    (by rw [hsChain_orbitSize]; rfl)
  rw [hb, ← hsP_eq_original] at htrans
  intro x y
  obtain ⟨g, hg, hgx⟩ := htrans x
  obtain ⟨h, hh, hhy⟩ := htrans y
  refine ⟨h * g⁻¹, hsP.mul_mem hh (hsP.inv_mem hg), ?_⟩
  have : g⁻¹ x = 0 := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hgx.symm
  rw [Equiv.Perm.mul_apply, this, hhy]

theorem tbl_inner {k j : Nat} (hj : j < 22) (hk : (bndAt j).1 = k) (ho : (bndAt j).2.2 = false)
    (hk43 : k < 43) : T k ∈ hsP := by
  have := bnd_eq hj (hk ▸ hk43)
  rw [ho, hk] at this
  simp only [Bool.false_eq_true, if_false] at this
  rw [this]
  exact E_mem' (valid_parts.1 j hj)

theorem tbl_outer {k j : Nat} (hj : j < 22) (hk : (bndAt j).1 = k) (ho : (bndAt j).2.2 = true)
    (hk43 : k < 43) : T k ∈ hsR ∧ T k ∉ hsP := by
  have := bnd_eq hj (hk ▸ hk43)
  rw [ho, hk] at this
  simp only [if_true] at this
  rw [this]
  have hE := E_mem' (valid_parts.1 j hj)
  refine ⟨mul_mem (P_le_R hE) U_mem_R, fun h => U_notMem ?_⟩
  have := hsP.mul_mem (hsP.inv_mem hE) h
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

noncomputable def gC (r k : Nat) : Equiv.Perm (Fin 3850) :=
  if k % 2 = 0 then T (ct r k) else (T (ct r k))⁻¹

theorem cb_ncg (r : Nat) (hr : r < 4) : 0 < ncg r ∧ cb r + ncg r ≤ 39 ∧ 1 ≤ cb r := by
  unfold cb ncg
  simp only [nIf_eq, beq_dec, decide_eq_true_eq]
  interval_cases r <;> simp

theorem ct_spec (r k : Nat) (hr : r < 4) : ∃ j < ncg r, ct r k = cb r + j :=
  ⟨_, Nat.mod_lt _ (cb_ncg r hr).1, rfl⟩

theorem ct_lt (r k : Nat) (hr : r < 4) : ct r k < 43 := by
  obtain ⟨j, hj, e⟩ := ct_spec r k hr
  have := cb_ncg r hr
  omega

theorem LC_rep (r k : Nat) (hr : r < 4) : RepF 3850 (LC r k) (gC r k) := by
  have e : LC r k = fun x => if k % 2 = 0 then tv (ct r k) x else ti (ct r k) x := by
    funext x
    unfold LC
    rw [nIf_eq, beq_dec]
    simp only [decide_eq_true_eq]
    rfl
  rw [e]
  unfold gC
  by_cases hk : k % 2 = 0
  · simp only [hk, if_true]
    exact (T_rep (ct_lt r k hr)).1
  · simp only [hk, if_false]
    exact (T_rep (ct_lt r k hr)).2

theorem gC_inv (r k : Nat) : gC r (ivL k) = (gC r k)⁻¹ := by
  have hct : ct r (ivL k) = ct r k := by
    have h2 : ivL k / 2 = k / 2 := by
      rw [ivL_eq]
      split_ifs <;> omega
    unfold ct
    change cb r + (ivL k / 2) % ncg r = cb r + (k / 2) % ncg r
    rw [h2]
  unfold gC
  rw [hct, ivL_eq]
  split_ifs with h1 h2 h2 <;> first | omega | simp

theorem eq_of_mul_le {a b c d : Nat} (ha : c ≤ a) (hb : d ≤ b) (h : a * b = c * d) (hc : 0 < c)
    (hd : 0 < d) : a = c ∧ b = d := by
  have h1 : c * b ≤ a * b := Nat.mul_le_mul_right b ha
  have h2 : c * b ≤ c * d := h ▸ h1
  have hbd : b = d := le_antisymm (Nat.le_of_mul_le_mul_left h2 hc) hb
  subst hbd
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) h, rfl⟩

section Record

variable {ri : Nat} (hri : ri < 4)
include hri

theorem rec_parts :
    eqOnL bsR (fun x => tR ri (tR ri x)) (fun x => x) = true ∧
    neL bsR (tR ri) (fun x => x) = true ∧
    (∀ j < ncg ri, eqOnL bsR (fun x => tv (Nat.add (cb ri) j) (tR ri x))
      (fun x => tR ri (tv (Nat.add (cb ri) j) x)) = true) ∧
    cntFix 3850 (tR ri) = HSD.fx.getD ri 0 ∧
    chainL 3850 (LC ri) (HSD.ch.getD ri []) [] = true ∧
    oddL bsR (LC ri) (HSD.od.getD ri []) = true := by
  have h := HSR.all ri hri
  unfold recB at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h3, h5, h7, h9, h10⟩ := h
  exact ⟨h1, h3, allN_spec h5, Nat.eq_of_beq_eq_true h7, h9, h10⟩

theorem data_parts :
    chainOrd ri = cnto ri ∧ clsz ri * HSD.fx.getD ri 0 = 3850 * (HSD.cf.getD ri []).length ∧
      (HSD.uc.getD ri (0, [])).1 < 4 ∧
      eqOnL bsR (cjv LP (HSD.uc.getD ri (0, [])).2 (fun x => uP (tR ri (uP x))))
        (tR (HSD.uc.getD ri (0, [])).1) = true := by
  have h := HSD4.all ri hri
  unfold dataB at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h3, h5, h6⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h3, Nat.blt_eq.mp h5, h6⟩

end Record

def cgOff (r : Nat) : Nat := [8, 10, 14, 18].getD r 0

theorem bnd_rep_data : ∀ r < 4, (bndAt (4 + r)).1 = rt r ∧ (bndAt (4 + r)).2.2 = decide (2 ≤ r) := by
  decide +kernel

theorem bnd_cg_data : ∀ r < 4, ∀ j < ncg r, cgOff r + j < 22 ∧ (bndAt (cgOff r + j)).1 = cb r + j ∧
    (bndAt (cgOff r + j)).2.2 = false := by
  decide +kernel

theorem bnd_s_data : ∀ l < 4, (bndAt l).1 = l + 1 := by
  decide +kernel

theorem fx_pos : ∀ r < 4, 0 < HSD.fx.getD r 0 := by
  decide +kernel

theorem rt_lt (r : Nat) (hr : r < 4) : rt r < 43 := by
  have := cb_ncg r hr
  unfold rt
  change cb r - 1 < 43
  omega

theorem rt_vals : rt 0 = 5 ∧ rt 1 = 12 ∧ rt 2 = 21 ∧ rt 3 = 34 := by decide

theorem cb_vals : cb 0 = 6 ∧ cb 1 = 13 ∧ cb 2 = 22 ∧ cb 3 = 35 := by decide

theorem ncg_vals : ncg 0 = 2 ∧ ncg 1 = 4 ∧ ncg 2 = 4 ∧ ncg 3 = 4 := by decide

theorem cnto_vals : cnto 0 = 7680 ∧ cnto 1 = 2880 ∧ cnto 2 = 40320 ∧ cnto 3 = 1920 := by decide

theorem clsz_vals : clsz 0 = 5775 ∧ clsz 1 = 15400 ∧ clsz 2 = 1100 ∧ clsz 3 = 23100 := by decide

section Main

variable {ri : Nat} (hri : ri < 4)
include hri

theorem tR_rep : RepF 3850 (tR ri) (T (rt ri)) := (T_rep (rt_lt ri hri)).1

theorem cg_lt {j : Nat} (hj : j < ncg ri) : cb ri + j < 43 := by
  have := cb_ncg ri hri
  omega

theorem cg_mem {j : Nat} (hj : j < ncg ri) : T (cb ri + j) ∈ hsP := by
  obtain ⟨h1, h2, h3⟩ := bnd_cg_data ri hri j hj
  exact tbl_inner h1 h2 h3 (cg_lt hri hj)

theorem t_mem : T (rt ri) ∈ hsR := by
  obtain ⟨h1, h2⟩ := bnd_rep_data ri hri
  by_cases h : 2 ≤ ri
  · exact (tbl_outer (by omega) h1 (by rw [h2]; simp [h]) (rt_lt ri hri)).1
  · exact P_le_R (tbl_inner (by omega) h1 (by rw [h2]; simp [h]) (rt_lt ri hri))

theorem t_outer : (decide (2 ≤ ri) = true) ↔ T (rt ri) ∉ hsP := by
  obtain ⟨h1, h2⟩ := bnd_rep_data ri hri
  by_cases h : 2 ≤ ri
  · simp only [h, decide_true, true_iff]
    exact (tbl_outer (by omega) h1 (by rw [h2]; simp [h]) (rt_lt ri hri)).2
  · simp only [h, decide_false, Bool.false_eq_true, false_iff, not_not]
    exact tbl_inner (by omega) h1 (by rw [h2]; simp [h]) (rt_lt ri hri)

theorem t_sq : T (rt ri) * T (rt ri) = 1 :=
  eqR ((tR_rep hri).comp (tR_rep hri)) RepF.one (mul_mem (t_mem hri) (t_mem hri)) (one_mem _)
    (rec_parts hri).1

theorem t_ne : T (rt ri) ≠ 1 := fun h =>
  neL_spec (rec_parts hri).2.1 ((eqOnL_iff _ _ _).1
    (eqOnL_of_eq bsR_lt (tR_rep hri) (h ▸ RepF.one)))

theorem t_ord : orderOf (T (rt ri)) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact t_sq hri) (t_ne hri)

theorem cg_comm {j : Nat} (hj : j < ncg ri) :
    T (rt ri) * T (cb ri + j) = T (cb ri + j) * T (rt ri) :=
  (eqR ((T_rep (cg_lt hri hj)).1.comp (tR_rep hri)) ((tR_rep hri).comp (T_rep (cg_lt hri hj)).1)
    (mul_mem (P_le_R (cg_mem hri hj)) (t_mem hri)) (mul_mem (t_mem hri) (P_le_R (cg_mem hri hj)))
    ((rec_parts hri).2.2.1 j hj)).symm

theorem conj_count :
    (conjClass hsP (T (rt ri))).ncard * HSD.fx.getD ri 0 =
      3850 * {y ∈ conjClass hsP (T (rt ri)) | y ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩}.ncard := by
  have h := ncard_conjClass_mul_fix hsP hs_trans (T (rt ri)) ⟨0, by norm_num⟩
  rw [← cntFix_card (tR_rep hri), (rec_parts hri).2.2.2.1] at h
  exact h

theorem fix0_ge : (HSD.cf.getD ri []).length ≤
    {y ∈ conjClass hsP (T (rt ri)) | y ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩}.ncard := by
  obtain ⟨h1, h2⟩ := cfL_spec (fun k => LP_rep k) gP_inv (by norm_num) (by norm_num)
    (tR_rep hri) (HSF.all ri hri)
  have := length_le_ncard_of_nodup h2 (S := {y ∈ conjClass hsP (T (rt ri)) |
    y ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩}) (fun x hx => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    exact ⟨mem_conjClass.2 ⟨_, wordVal_mem gP_mem w, rfl⟩, h1 w hw⟩)
  rwa [List.length_map] at this

theorem class_ge : clsz ri ≤ (conjClass hsP (T (rt ri))).ncard := by
  have h1 := conj_count hri
  have h2 := fix0_ge hri
  have h3 := (data_parts hri).2.1
  have h4 := fx_pos ri hri
  by_contra hlt
  push_neg at hlt
  have : (conjClass hsP (T (rt ri))).ncard * HSD.fx.getD ri 0 < clsz ri * HSD.fx.getD ri 0 :=
    Nat.mul_lt_mul_of_pos_right hlt h4
  omega

end Main

section MainC

variable {ri : Nat} (hri : ri < 4) {row : ClassRow}
  (hcg : row.centGens = (List.range (ncg ri)).map (fun j => hsCentTbl (cb ri + j)))
include hri hcg

theorem C_le : CFSG.Sporadic.SmallOddCore.hsC row ≤
    hsP ⊓ centralizer ({T (rt ri)} : Set (Equiv.Perm (Fin 3850))) := by
  unfold CFSG.Sporadic.SmallOddCore.hsC
  rw [closure_le, Set.image_subset_iff]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_toArray] at hx
  rw [hcg, List.mem_map] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  rw [List.mem_range] at hj
  rw [Set.mem_preimage, ← hxj]
  exact mem_inf.2 ⟨cg_mem hri hj, mem_centralizer_singleton_iff.2 (cg_comm hri hj).symm⟩

theorem gC_memC (k : Nat) : gC ri k ∈ CFSG.Sporadic.SmallOddCore.hsC row := by
  obtain ⟨j, hj, e⟩ := ct_spec ri k hri
  have hT : T (cb ri + j) ∈ CFSG.Sporadic.SmallOddCore.hsC row := by
    refine subset_closure ⟨hsCentTbl (cb ri + j), ?_, rfl⟩
    simp only [Set.mem_setOf_eq, List.mem_toArray]
    rw [hcg, List.mem_map]
    exact ⟨j, List.mem_range.2 hj, rfl⟩
  unfold gC
  rw [e]
  split_ifs
  · exact hT
  · exact inv_mem hT

theorem C_card_ge : cnto ri ≤ Nat.card (CFSG.Sporadic.SmallOddCore.hsC row) := by
  have h := chainL_card (fun k => LC_rep ri k hri) (by norm_num) (gC_memC hri hcg)
    (rec_parts hri).2.2.2.2.1
  rw [← (data_parts hri).1]
  exact h

theorem rec_main (hNP : clsz ri * cnto ri = 44352000) :
    CFSG.Sporadic.SmallOddCore.hsC row =
      hsP ⊓ centralizer ({T (rt ri)} : Set (Equiv.Perm (Fin 3850))) ∧
      Nat.card ↥(hsP ⊓ centralizer ({T (rt ri)} : Set (Equiv.Perm (Fin 3850)))) = cnto ri ∧
      (conjClass hsP (T (rt ri))).ncard = clsz ri := by
  have hle := C_le hri hcg
  have hcard := Subgroup.card_le_of_le hle
  have hos := ncard_conjClass_mul_card hsP (T (rt ri))
  rw [card_hsP, ← hNP] at hos
  have hpos1 : 0 < clsz ri := by
    rcases Nat.eq_zero_or_pos (clsz ri) with h | h
    · rw [h, Nat.zero_mul] at hNP
      exact absurd hNP (by norm_num)
    · exact h
  have hpos2 : 0 < cnto ri := by
    rcases Nat.eq_zero_or_pos (cnto ri) with h | h
    · rw [h, Nat.mul_zero] at hNP
      exact absurd hNP (by norm_num)
    · exact h
  obtain ⟨e1, e2⟩ := eq_of_mul_le (class_ge hri) ((C_card_ge hri hcg).trans hcard) hos hpos1 hpos2
  refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, e2, e1⟩
  rw [e2]
  exact C_card_ge hri hcg

end MainC

theorem gC_memK {ri : Nat} (hri : ri < 4) (k : Nat) :
    gC ri k ∈ hsP ⊓ centralizer ({T (rt ri)} : Set (Equiv.Perm (Fin 3850))) := by
  obtain ⟨j, hj, e⟩ := ct_spec ri k hri
  have hT : T (cb ri + j) ∈ hsP ⊓ centralizer ({T (rt ri)} : Set (Equiv.Perm (Fin 3850))) :=
    mem_inf.2 ⟨cg_mem hri hj, mem_centralizer_singleton_iff.2 (cg_comm hri hj).symm⟩
  unfold gC
  rw [e]
  split_ifs
  · exact hT
  · exact inv_mem hT

@[expose] def WK (K : Subgroup (Equiv.Perm (Fin 3850))) (x : Equiv.Perm (Fin 3850)) : Prop :=
  ∃ h ∈ K, 2 ∣ orderOf (x * (h * x * h⁻¹))

section Odd

variable {K : Subgroup (Equiv.Perm (Fin 3850))} (hKR : K ≤ hsR) {L : Nat → Nat → Nat}
  {g : Nat → Equiv.Perm (Fin 3850)} (hL : ∀ k, RepF 3850 (L k) (g k))
  (hi : ∀ k, g (ivL k) = (g k)⁻¹) (hg : ∀ k, g k ∈ K)
include hKR hL hi hg

theorem witL_spec {y : List Nat} {hm : List Nat × Nat} (h : witL bsR L y hm = true) :
    WK K (wordVal g y) := by
  have hy := wordVal_mem hg y
  have hh := wordVal_mem hg hm.1
  refine ⟨wordVal g hm.1, hh, evenOrd_spec faithR bsR_lt (conjProd_rep hL hi y hm.1)
    (hKR (mul_mem hy (mul_mem (mul_mem hh hy) (inv_mem hh)))) h⟩

theorem ne_of_neL {v w : List Nat} (h : neL bsR (wv L v) (wv L w) = true) :
    wordVal g v ≠ wordVal g w := fun e =>
  neL_spec h ((eqOnL_iff _ _ _).1 (eqOnL_of_eq bsR_lt (wv_rep hL v) (e ▸ wv_rep hL w)))

theorem oddE_cyc {e : Nat × List (List Nat) × List (List Nat × Nat)} (h : oddE bsR L e = true)
    (hlen : e.2.1.length = 1) (hp : e.1.Prime) :
    orderOf (wordVal g (e.2.1.getD 0 [])) = e.1 ∧ WK K (wordVal g (e.2.1.getD 0 [])) := by
  have h' : bAnd(ordPL bsR (wv L (e.2.1.getD 0 [])) e.1,
      witL bsR L (e.2.1.getD 0 []) (e.2.2.getD 0 ([], 0))) = true := by
    unfold oddE at h
    rw [hlen] at h
    exact h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
  exact ⟨(ordPL_iff faithR bsR_lt (wv_rep hL _) (hKR (wordVal_mem hg _)) hp).1 h1,
    witL_spec hKR hL hi hg h2⟩

theorem oddE_nine {e : Nat × List (List Nat) × List (List Nat × Nat)} (h : oddE bsR L e = true)
    (hlen : e.2.1.length ≠ 1) :
    e.1 = 3 ∧ orderOf (wordVal g (e.2.1.getD 0 [])) = 3 ∧
      orderOf (wordVal g (e.2.1.getD 1 [])) = 3 ∧
      Commute (wordVal g (e.2.1.getD 0 [])) (wordVal g (e.2.1.getD 1 [])) ∧
      wordVal g (e.2.1.getD 1 []) ∉ zpowers (wordVal g (e.2.1.getD 0 [])) ∧
      WK K (wordVal g (e.2.1.getD 0 [])) ∧ WK K (wordVal g (e.2.1.getD 1 [])) ∧
      WK K (wordVal g (e.2.1.getD 0 []) * wordVal g (e.2.1.getD 1 [])) ∧
      WK K (wordVal g (e.2.1.getD 0 []) * wordVal g (e.2.1.getD 1 []) *
        wordVal g (e.2.1.getD 1 [])) := by
  have hb : Nat.beq e.2.1.length 1 = false := by
    cases e' : Nat.beq e.2.1.length 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e') hlen
  unfold oddE at h
  rw [hb] at h
  simp only [bAnd_iff] at h
  obtain ⟨-, h3, h4, h5, h6, h7, h8, w1, w2, w3, w4⟩ := h
  set v := e.2.1.getD 0 []
  set w := e.2.1.getD 1 []
  have he : e.1 = 3 := Nat.eq_of_beq_eq_true h3
  have hv := wordVal_mem hg v
  have hw := wordVal_mem hg w
  have o1 := (ordPL_iff faithR bsR_lt (wv_rep hL v) (hKR hv) Nat.prime_three).1 h4
  have o2 := (ordPL_iff faithR bsR_lt (wv_rep hL w) (hKR hw) Nat.prime_three).1 h5
  have hc : wordVal g v * wordVal g w = wordVal g w * wordVal g v := by
    have := eqR (wv_rep hL (v ++ w)) (wv_rep hL (w ++ v)) (hKR (wordVal_mem hg _))
      (hKR (wordVal_mem hg _)) h6
    rwa [wordVal_append, wordVal_append] at this
  have n1 := ne_of_neL hKR hL hi hg h7
  have n2 := ne_of_neL hKR hL hi hg h8
  rw [wordVal_append] at n2
  have hnz : wordVal g w ∉ zpowers (wordVal g v) := by
    intro hm
    rw [mem_zpowers_iff_mem_range_orderOf, o1, Finset.mem_image] at hm
    obtain ⟨k, hk, hkw⟩ := hm
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero] at hkw
      rw [← hkw, orderOf_one] at o2
      exact absurd o2 (by norm_num)
    · rw [pow_one] at hkw
      exact n1 hkw.symm
    · rw [sq] at hkw
      exact n2 hkw.symm
  have w3' := witL_spec hKR hL hi hg w3
  have w4' := witL_spec hKR hL hi hg w4
  rw [wordVal_append] at w3'
  rw [wordVal_append, wordVal_append] at w4'
  exact ⟨he, o1, o2, hc, hnz, witL_spec hKR hL hi hg w1, witL_spec hKR hL hi hg w2, w3', w4'⟩

end Odd

noncomputable def gS (k : Nat) : Equiv.Perm (Fin 3850) :=
  if k % 2 = 0 then T (st k) else (T (st k))⁻¹

theorem st_lt (k : Nat) : 1 ≤ st k ∧ st k < 5 := by
  unfold st
  change 1 ≤ (k / 2) % 4 + 1 ∧ (k / 2) % 4 + 1 < 5
  omega

theorem LS_rep (k : Nat) : RepF 3850 (LS k) (gS k) := by
  have e : LS k = fun x => if k % 2 = 0 then tv (st k) x else ti (st k) x := by
    funext x
    unfold LS
    rw [nIf_eq, beq_dec]
    simp only [decide_eq_true_eq]
    rfl
  have hk : st k < 43 := by have := st_lt k; omega
  rw [e]
  unfold gS
  by_cases h : k % 2 = 0
  · simp only [h, if_true]
    exact (T_rep hk).1
  · simp only [h, if_false]
    exact (T_rep hk).2

theorem gS_inv (k : Nat) : gS (ivL k) = (gS k)⁻¹ := by
  have hst : st (ivL k) = st k := by
    have h2 : ivL k / 2 = k / 2 := by
      rw [ivL_eq]
      split_ifs <;> omega
    unfold st
    change (ivL k / 2) % 4 + 1 = (k / 2) % 4 + 1
    rw [h2]
  unfold gS
  rw [hst, ivL_eq]
  split_ifs with h1 h2 h2 <;> first | omega | simp

theorem sgen_eq : (tp 3850 '' {x | x ∈ hsSylowGenTbls.toArray}) = {T 1, T 2, T 3, T 4} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_toArray, hsSylowGenTbls, List.mem_map,
    List.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    interval_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, ⟨0, by norm_num, rfl⟩, rfl⟩
    · exact ⟨_, ⟨1, by norm_num, rfl⟩, rfl⟩
    · exact ⟨_, ⟨2, by norm_num, rfl⟩, rfl⟩
    · exact ⟨_, ⟨3, by norm_num, rfl⟩, rfl⟩

theorem gS_memS (k : Nat) : gS k ∈ hsS := by
  have hT : T (st k) ∈ hsS := by
    unfold hsS
    rw [sgen_eq]
    refine subset_closure ?_
    have := st_lt k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have h : st k = 1 ∨ st k = 2 ∨ st k = 3 ∨ st k = 4 := by omega
    rcases h with h | h | h | h <;> rw [h] <;> simp
  unfold gS
  split_ifs
  · exact hT
  · exact inv_mem hT

theorem tbl_R {j : Nat} (hj : j < 22) (hk : (bndAt j).1 < 43) : T (bndAt j).1 ∈ hsR := by
  rw [bnd_eq hj hk]
  have hE := E_mem' (valid_parts.1 j hj)
  split_ifs
  · exact mul_mem (P_le_R hE) U_mem_R
  · exact P_le_R hE

theorem S_le_R : hsS ≤ hsR := by
  unfold hsS
  rw [sgen_eq, closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  have h := fun l (hl : l < 4) => tbl_R (j := l) (by omega) (by rw [bnd_s_data l hl]; omega)
  rcases hy with rfl | rfl | rfl | rfl
  · have := h 0 (by norm_num); rwa [bnd_s_data 0 (by norm_num)] at this
  · have := h 1 (by norm_num); rwa [bnd_s_data 1 (by norm_num)] at this
  · have := h 2 (by norm_num); rwa [bnd_s_data 2 (by norm_num)] at this
  · have := h 3 (by norm_num); rwa [bnd_s_data 3 (by norm_num)] at this

theorem sRun_spec : ∀ (ws : List (List Nat)) (i₀ : Nat) (cs : List (Nat × List Nat)),
    sRun i₀ ws cs = true → ∀ k < ws.length, sAt (i₀ + k) (ws.getD k []) (cs.getD k (0, [])) = true
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | w :: ws, i₀, cs, h, k, hk => by
    have h' : Bool.rec (motive := fun _ => Bool) false (sRun (Nat.succ i₀) ws cs.tail)
        (sAt i₀ w (cs.headD (0, []))) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases k with _ | k
    · cases cs <;> simpa using h1
    · have := sRun_spec ws (i₀ + 1) cs.tail h2 k (by simpa using hk)
      cases cs <;> simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem sort_parts : HSD.sw.length = 1024 ∧ HSD.sc.length = 1024 ∧
    sortK 1024 sK sS sSI = true := by
  have h := sort_ok
  unfold sortB at h
  simp only [bAnd_iff] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, h4⟩

theorem s_at {i : Nat} (hi : i < 1024) :
    sAt i (HSD.sw.getD i []) (HSD.sc.getD i (0, [])) = true := by
  have h := sB_all (i / 64) (show i / 64 < 16 by omega) ((i / 8) % 8)
    (show (i / 8) % 8 < 8 from Nat.mod_lt _ (by norm_num))
  unfold sB at h
  rw [strictB_val] at h
  have hi0 : Nat.mul (Nat.add (Nat.mul (i / 64) 8) ((i / 8) % 8)) 8 + i % 8 = i := by
    change ((i / 64) * 8 + (i / 8) % 8) * 8 + i % 8 = i
    omega
  have hl := sort_parts
  have := sRun_spec _ _ _ h (i % 8) (by
    rw [List.length_take, List.length_drop, hl.1]
    change i % 8 < min 8 (1024 - ((i / 64) * 8 + (i / 8) % 8) * 8)
    omega)
  rw [hi0] at this
  have e1 : ((HSD.sw.drop (Nat.mul (Nat.add (Nat.mul (i / 64) 8) ((i / 8) % 8)) 8)).take 8).getD
      (i % 8) [] = HSD.sw.getD i [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (Nat.mod_lt _ (by norm_num)),
      List.getElem?_drop, hi0, ← List.getD_eq_getElem?_getD]
  have e2 : ((HSD.sc.drop (Nat.mul (Nat.add (Nat.mul (i / 64) 8) ((i / 8) % 8)) 8)).take 8).getD
      (i % 8) (0, []) = HSD.sc.getD i (0, []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (Nat.mod_lt _ (by norm_num)),
      List.getElem?_drop, hi0, ← List.getD_eq_getElem?_getD]
  rwa [e1, e2] at this

noncomputable def eS (i : Nat) : Equiv.Perm (Fin 3850) := wordVal gS (HSD.sw.getD i [])

theorem eS_rep (i : Nat) : RepF 3850 (wv LS (HSD.sw.getD i [])) (eS i) := wv_rep LS_rep _

theorem eS_mem (i : Nat) : eS i ∈ hsS := wordVal_mem gS_memS _

theorem keyL_lt {f : Nat → Nat} {x : Equiv.Perm (Fin 3850)} (hf : RepF 3850 f x) :
    ∀ b ∈ bsR, f b < 3850 := fun b hb => hf.lt (bsR_lt b hb)

theorem eqOnL_of_keyL {f f' : Nat → Nat} {x y : Equiv.Perm (Fin 3850)} (hf : RepF 3850 f x)
    (hf' : RepF 3850 f' y) (h : keyL 3850 f bsR = keyL 3850 f' bsR) : eqOnL bsR f f' = true := by
  rw [ClP.keyL_eq, ClP.keyL_eq] at h
  have := imgKey_inj (n := 3850) (by simp) (by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hv
    exact keyL_lt hf b hb) (by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hv
    exact keyL_lt hf' b hb) h
  refine (eqOnL_iff _ _ _).2 fun b hb => ?_
  have := congrArg (fun l => l.getD (bsR.idxOf b) 0) this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf hb, Option.map_some, Option.getD_some] at this
  exact this

theorem s_parts {i : Nat} (hi : i < 1024) :
    sK i = keyL 3850 (wv LS (HSD.sw.getD i [])) bsR ∧
    (∀ l < 4, sM (Nat.add (Nat.mul i 4) l) < 1024 ∧ sK (sM (Nat.add (Nat.mul i 4) l)) =
      keyL 3850 (fun x => wv LS (HSD.sw.getD i []) (LS (Nat.mul l 2) x)) bsR) ∧
    ((eqOnL bsR (fun x => wv LS (HSD.sw.getD i []) (wv LS (HSD.sw.getD i []) x)) (fun x => x) =
        true ∧ neL bsR (wv LS (HSD.sw.getD i [])) (fun x => x) = true) →
      (HSD.sc.getD i (0, [])).1 < 4 ∧ eqOnL bsR (cjv LP (HSD.sc.getD i (0, [])).2
        (wv LS (HSD.sw.getD i []))) (tR (HSD.sc.getD i (0, [])).1) = true) := by
  have h := s_at hi
  unfold sAt at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  refine ⟨Nat.eq_of_beq_eq_true h1, fun l hl => ?_, fun hc => ?_⟩
  · have := allN_spec h3 l hl
    rw [strictB_val] at this
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
    exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩
  · rw [show bAnd(eqOnL bsR (fun x => wv LS (HSD.sw.getD i []) (wv LS (HSD.sw.getD i []) x))
        (fun x => x), neL bsR (wv LS (HSD.sw.getD i [])) (fun x => x)) = true from
        (bAnd_iff _ _).2 hc] at h4
    exact (bAnd_iff _ _).1 h4 |>.imp Nat.blt_eq.mp id

theorem eS_inj {i j : Nat} (hi : i < 1024) (hj : j < 1024) (h : eS i = eS j) : i = j := by
  refine sortK_inj sort_parts.2.2 i hi j hj ?_
  rw [(s_parts hi).1, (s_parts hj).1]
  refine ClP.keyL_eq _ _ _ ▸ ClP.keyL_eq _ _ _ ▸ ?_
  rw [ClP.keyL_eq, ClP.keyL_eq]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  rw [eS_rep i b (bsR_lt b hb), eS_rep j b (bsR_lt b hb), h]

theorem eS_zero : eS 0 = 1 := by
  have : HSD.sw.getD 0 [] = [] := by decide +kernel
  rw [eS, this, wordVal_nil]

theorem eS_mul {i : Nat} (hi : i < 1024) {l : Nat} (hl : l < 4) :
    eS i * T (l + 1) = eS (sM (Nat.add (Nat.mul i 4) l)) := by
  obtain ⟨hm, hk⟩ := (s_parts hi).2.1 l hl
  have hgl : gS (Nat.mul l 2) = T (l + 1) := by
    unfold gS st
    have : Nat.mul l 2 % 2 = 0 := by change l * 2 % 2 = 0; omega
    rw [if_pos this]
    congr 2
    change (l * 2 / 2) % 4 = l
    omega
  have hrep : RepF 3850 (fun x => wv LS (HSD.sw.getD i []) (LS (Nat.mul l 2) x)) (eS i * T (l + 1)) :=
    hgl ▸ (eS_rep i).comp (LS_rep _)
  rw [(s_parts hm).1] at hk
  exact eqR hrep (eS_rep _) (mul_mem (S_le_R (eS_mem i)) (S_le_R (hgl ▸ gS_memS _)))
    (S_le_R (eS_mem _)) (eqOnL_of_keyL hrep (eS_rep _) hk.symm)

theorem S_enum : ∀ x ∈ hsS, ∃ i < 1024, x = eS i := by
  unfold hsS
  rw [sgen_eq]
  refine mem_of_enum ⟨0, by norm_num, eS_zero⟩ fun i hi s hs => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨_, (s_parts hi).2.1 0 (by norm_num) |>.1, eS_mul hi (l := 0) (by norm_num)⟩
  · exact ⟨_, (s_parts hi).2.1 1 (by norm_num) |>.1, eS_mul hi (l := 1) (by norm_num)⟩
  · exact ⟨_, (s_parts hi).2.1 2 (by norm_num) |>.1, eS_mul hi (l := 2) (by norm_num)⟩
  · exact ⟨_, (s_parts hi).2.1 3 (by norm_num) |>.1, eS_mul hi (l := 3) (by norm_num)⟩

theorem card_S : Nat.card hsS = 1024 := by
  have hset : (hsS : Set (Equiv.Perm (Fin 3850))) = eS '' ((Finset.range 1024 : Finset ℕ) : Set ℕ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := S_enum x hx
      exact ⟨i, by simpa using hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      exact eS_mem i
  have hinj : Set.InjOn eS ((Finset.range 1024 : Finset ℕ) : Set ℕ) := fun i hi j hj h =>
    eS_inj (by simpa using hi) (by simpa using hj) h
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, hinj.ncard_image, Set.ncard_coe_finset,
    Finset.card_range]

end HS

end CertificateChecks.KernelSporSch.HS72

end
