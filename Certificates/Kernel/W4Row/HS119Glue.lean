module

public import Certificates.Kernel.W4Row.HS119Model
public import Certificates.Kernel.W4Row.HS119Cert
public import Certificates.Kernel.SporSch.PairHS.HS2272Facts
public import CFSG.Certificates.Kernel.W4Row.HS119KSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

set_option maxRecDepth 4000

namespace CFSG.KD.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.HS119 CFSG.KD.LQT.C4126 CFSG.KS.SporSch
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CertificateChecks.KernelSporSch

noncomputable abbrev sg (l : ℕ) : Equiv.Perm (Fin 3850) := HS72.T (Nat.succ l)

@[expose] noncomputable def e (k : ℕ) : Equiv.Perm (Fin 3850) := eF SPA sg 9 k

noncomputable abbrev Gt (l : ℕ) : ℕ := HC.F (Nat.succ l)

noncomputable abbrev GIt (l : ℕ) : ℕ := HCI (Nat.succ l)

theorem tree : ∀ k < 1024, k ≠ 0 → Nat.land (SPA k) 16777215 < k ∧
    Nat.shiftRight (SPA k) 24 < 4 ∧
      SE k = mul 32 (SE (Nat.land (SPA k) 16777215)) (SG (Nat.shiftRight (SPA k) 24)) :=
  fun k hk hk0 => treeAt_spec ((allN_iff _ _).1 s_tree k hk) hk0

theorem tree' : ∀ k < 1024, k ≠ 0 → Nat.land (SPA k) 16777215 < k ∧
    Nat.shiftRight (SPA k) 24 < 4 :=
  fun k hk hk0 => ⟨(tree k hk hk0).1, (tree k hk hk0).2.1⟩

theorem SE_zero : SE 0 = one 32 := treeAt_zero ((allN_iff _ _).1 s_tree 0 (by norm_num))

theorem sg_rep {l : ℕ} (hl : l < 4) : RepF 3850 (fun x => fd 12 (Gt l) x) (sg l) := by
  rw [fun_fd_eq_pg]
  exact (HS72.T_rep (k := Nat.succ l) (by omega)).1

theorem sgI_rep {l : ℕ} (hl : l < 4) : RepF 3850 (fun x => fd 12 (GIt l) x) (sg l)⁻¹ := by
  rw [fun_fd_eq_pg]
  exact (HS72.T_rep (k := Nat.succ l) (by omega)).2

theorem e_rep {k : ℕ} (hk : k < 1024) : RepF 3850 (evS SPA Gt 9 k) (e k) :=
  evS_rep tree' (fun l hl => sg_rep hl) 9 k hk

theorem eI_rep {k : ℕ} (hk : k < 1024) : RepF 3850 (evSI SPA GIt 9 k) (e k)⁻¹ :=
  evSI_rep tree' (fun l hl => sgI_rep hl) 9 k hk

theorem dep {k : ℕ} (hk : k < 1024) : parK SPA 0 9 k < 2 :=
  Nat.blt_eq.mp ((allN_iff _ _).1 c_dep k hk)

section HS


theorem sg_memS {l : ℕ} (hl : l < 4) : sg l ∈ hsS := by
  unfold hsS
  rw [HS72.sgen_eq]
  refine Subgroup.subset_closure ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases l <;> simp

theorem e_memS {k : ℕ} (hk : k < 1024) : e k ∈ hsS :=
  eF_mem tree' (fun l hl => sg_memS hl) 9 k hk

theorem e_memR {k : ℕ} (hk : k < 1024) : e k ∈ hsR := HS72.S_le_R (e_memS hk)

end HS

theorem om_step {i : ℕ} (hi : i < 31) : Om i < Om (i + 1) := by
  have h := (allN_iff _ _).1 s_om i (by omega)
  unfold omAt at h
  rw [Nat.blt_eq.mpr hi] at h
  exact Nat.blt_eq.mp h

theorem om_last : Om 31 < 3850 := by
  have h := (allN_iff _ _).1 s_om 31 (by norm_num)
  exact Nat.blt_eq.mp h

theorem om_lt {i : ℕ} (hi : i < 32) : Om i < 3850 := by
  have key : ∀ d i, i + d = 31 → Om i < 3850 := by
    intro d
    induction d with
    | zero => intro i hi; rw [Nat.add_zero] at hi; subst hi; exact om_last
    | succ d ih => intro i hi; exact (om_step (by omega)).trans (ih (i + 1) (by omega))
  exact key (31 - i) i (by omega)

theorem om_mono {i j : ℕ} (hij : i < j) (hj : j < 32) : Om i < Om j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact (ih h (by omega)).trans (om_step (by omega))
    · exact om_step (by omega)

theorem om_inj {i j : ℕ} (hi : i < 32) (hj : j < 32) (h : Om i = Om j) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd h (om_mono hij hj).ne
  · exact hij
  · exact absurd h (om_mono hij hi).ne'

@[expose] noncomputable def omF (i : ℕ) (hi : i < 32) : Fin 3850 := ⟨Om i, om_lt hi⟩

theorem rho : ∀ l < 4, ∀ i < 32, fd 12 (Gt l) (Om i) = Om (img (SG l) i) := fun l hl i hi =>
  Nat.eq_of_beq_eq_true ((allN_iff _ _).1 ((allN_iff _ _).1 s_rho l hl) i hi)

theorem e_om {k : ℕ} (hk : k < 1024) {i : ℕ} (hi : i < 32) :
    (e k (omF i hi) : ℕ) = Om (img (SE k) i) := by
  rw [← evS_om SE_zero tree rho 9 k hk (dep hk) i hi]
  exact ((e_rep hk) (Om i) (om_lt hi)).symm

theorem SE_code {k : ℕ} (hk : k < 1024) : ∃ σ : Equiv.Perm (Fin 32), code σ = SE k :=
  code_of_tree SE_zero tree (fun l hl => (allN_iff _ _).1 s_perm l hl) k hk

theorem SE_distinct {i j : ℕ} (hi : i < 1024) (hj : j < 1024) (h : SE i = SE j) : i = j :=
  CFSG.KC.Misc.Clos.sort_distinct (fun i hi => (allN_iff _ _).1 s_sort i hi) i hi j hj h

theorem idx_eq_of_om {a b : ℕ} (ha : a < 1024) (hb : b < 1024)
    (h : ∀ i (hi : i < 32), e a (omF i hi) = e b (omF i hi)) : a = b := by
  obtain ⟨σ, hσ⟩ := SE_code ha
  obtain ⟨τ, hτ⟩ := SE_code hb
  refine SE_distinct ha hb ?_
  have hst : σ = τ := by
    refine Equiv.ext fun i => Fin.ext ?_
    have h1 := congrArg Fin.val (h i i.isLt)
    rw [e_om ha, e_om hb, ← hσ, ← hτ] at h1
    have h2 := om_inj (img_lt _ _) (img_lt _ _) h1
    rwa [img_code (by norm_num), img_code (by norm_num)] at h2
  rw [← hσ, ← hτ, hst]

theorem e_inj {a b : ℕ} (ha : a < 1024) (hb : b < 1024) (h : e a = e b) : a = b :=
  idx_eq_of_om ha hb fun i hi => by rw [h]

section HS2


theorem S_enum {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsS) : ∃ k < 1024, x = e k := by
  have hsub : e '' ((Finset.range 1024 : Finset ℕ) : Set ℕ) ⊆ (hsS : Set (Equiv.Perm (Fin 3850))) := by
    rintro _ ⟨k, hk, rfl⟩
    exact e_memS (by simpa using hk)
  have hinj : Set.InjOn e ((Finset.range 1024 : Finset ℕ) : Set ℕ) := fun a ha b hb h =>
    e_inj (by simpa using ha) (by simpa using hb) h
  have hcard : (hsS : Set (Equiv.Perm (Fin 3850))).ncard ≤
      (e '' ((Finset.range 1024 : Finset ℕ) : Set ℕ)).ncard := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range, ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, HS72.card_S]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hx' : x ∈ e '' ((Finset.range 1024 : Finset ℕ) : Set ℕ) := by
    rw [heq]
    exact hx
  obtain ⟨k, hk, rfl⟩ := hx'
  exact ⟨k, by simpa using hk, rfl⟩

theorem eq_of_om {x y : Equiv.Perm (Fin 3850)} (hx : x ∈ hsS) (hy : y ∈ hsS)
    (h : ∀ i (hi : i < 32), x (omF i hi) = y (omF i hi)) : x = y := by
  obtain ⟨a, ha, rfl⟩ := S_enum hx
  obtain ⟨b, hb, rfl⟩ := S_enum hy
  rw [idx_eq_of_om ha hb h]

theorem e_mul {a b m : ℕ} (ha : a < 1024) (hb : b < 1024) (hm : m < 1024)
    (h : mul 32 (SE a) (SE b) = SE m) : e a * e b = e m := by
  refine eq_of_om (hsS.mul_mem (e_memS ha) (e_memS hb)) (e_memS hm) fun i hi => Fin.ext ?_
  have hb' : e b (omF i hi) = omF (img (SE b) i) (img_lt _ _) := Fin.ext (e_om hb hi)
  rw [Equiv.Perm.mul_apply, hb', e_om ha, e_om hm, ← h, img_mul32 hi]

end HS2

theorem hz1 : HZ 1 = 5 := by decide +kernel

theorem eq5_eqOnL {f g : ℕ → ℕ} (h : eq5 (HZ 1) f g = true) : eqOnL HS72.bsR f g = true := by
  obtain ⟨h0, h1, h2, h3, h5⟩ := eq5_spec h
  rw [hz1] at h5
  refine (eqOnL_iff _ _ _).2 fun b hb => ?_
  simp only [HS72.bsR, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h5]

section HS3


theorem eqR5 {f g : ℕ → ℕ} {x y : Equiv.Perm (Fin 3850)} (hf : RepF 3850 f x)
    (hg : RepF 3850 g y) (hx : x ∈ hsR) (hy : y ∈ hsR) (h : eq5 (HZ 1) f g = true) : x = y :=
  HS72.eqR hf hg hx hy (eq5_eqOnL h)

end HS3

theorem a_rep {j : ℕ} (hj : j < 2) : RepF 3850 (fun x => fd 12 (HS.F j) x) (hsGen j) ∧
    RepF 3850 (fun x => fd 12 (HSI j) x) (hsGen j)⁻¹ := by
  obtain ⟨-, h2⟩ := CFSG.KS.Prim.invEqK_sound (CFSG.KS.allN_spec hs_perms j hj)
  obtain ⟨r1, r2⟩ := CFSG.Monster.B.Co2.rep_permOfArr h2
  have e1 : hsGen j = CFSG.Monster.B.Co2.permOfArr 3850 (CFSG.KS.Raw.unpack 3850 12 (HS.F j)) := by
    rw [← hsStrong_get hj]
    rfl
  rw [e1, fun_fd_eq_pg, fun_fd_eq_pg]
  exact ⟨HS72.repF_unpack r1, HS72.repF_unpack r2⟩

noncomputable abbrev lE (c : ℕ) : Equiv.Perm (Fin 3850) := letE e hsGen c

theorem evH_rep {c : ℕ} (hc : 2 ≤ Nat.shiftRight c 10 → Nat.land c 1023 < 2) :
    RepF 3850 (evH c) (lE c) :=
  evL_rep (fun v hv => ⟨e_rep hv, eI_rep hv⟩) (fun j hj => a_rep hj) hc

theorem small_parts {c : ℕ} (hc : c < 1024) : Nat.shiftRight c 10 = 0 ∧ Nat.land c 1023 = c := by
  constructor
  · change c >>> 10 = 0
    rw [Nat.shiftRight_eq_div_pow]
    omega
  · change c &&& (2 ^ 10 - 1) = c
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega

theorem lE_small {c : ℕ} (hc : c < 1024) : lE c = e c := by
  obtain ⟨h1, h2⟩ := small_parts hc
  unfold lE letE
  rw [if_pos h1, h2]

theorem evH_small {c : ℕ} (hc : c < 1024) : RepF 3850 (evH c) (e c) := by
  have h := evH_rep (c := c) (fun h2 => by rw [(small_parts hc).1] at h2; omega)
  rwa [lE_small hc] at h

theorem aLet_parts {c : ℕ} (h : aLetOK c = true) :
    (Nat.shiftRight c 10 = 2 ∨ Nat.shiftRight c 10 = 3) ∧ Nat.land c 1023 < 2 := by
  unfold aLetOK at h
  rw [andB_iff, andB_iff, blt_iff, blt_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h1' : 2048 ≤ c := Nat.le_of_ble_eq_true h1
  have h2' : c < 4096 := h2
  refine ⟨?_, h3⟩
  change c >>> 10 = 2 ∨ c >>> 10 = 3
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem lE_memP {c : ℕ} (h : aLetOK c = true) : lE c ∈ hsP := by
  obtain ⟨ht, hv⟩ := aLet_parts h
  have hg : hsGen (Nat.land c 1023) ∈ hsP := by
    rw [hsP]
    refine Subgroup.subset_closure ?_
    interval_cases (Nat.land c 1023) <;> simp
  unfold lE letE
  rcases ht with ht | ht
  · rw [if_neg (by omega), if_neg (by omega), if_pos ht]
    exact hg
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hsP.inv_mem hg

noncomputable abbrev wA (W : ℕ) : Equiv.Perm (Fin 3850) := wE lE W (fd 12 W 0)

theorem wA_rep {W : ℕ} (h : wordOK aLetOK W = true) : RepF 3850 (evW evH W) (wA W) :=
  evW_rep fun i hi => evH_rep fun _ => (aLet_parts (wordOK_spec h i hi)).2

theorem wA_memP {W : ℕ} (h : wordOK aLetOK W = true) : wA W ∈ hsP :=
  wE_mem (fun i hi => lE_memP (wordOK_spec h i hi)) _ le_rfl

section HS4


theorem z_parts : HZ 0 < 1024 ∧ HZ 1 < 3850 ∧ (∀ q < 4, evH (HZ 0) q = q) ∧
    evH (HZ 0) (HZ 1) ≠ HZ 1 := by
  have h := c_z
  unfold zAt at h
  rw [andB_iff, andB_iff, andB_iff, blt_iff, blt_iff, allN_iff, notB_iff, beq_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, fun q hq => beq_iff.1 (h3 q hq), h4⟩

theorem ez_notMem : e (HZ 0) ∉ hsP := by
  obtain ⟨h1, h2, h3, h4⟩ := z_parts
  intro hP
  rw [HS72.P_eq] at hP
  have hrep := evH_small h1
  have h1' := hs_baseFaithful _ hP fun x hx => by
    refine Fin.ext ?_
    have hx4 : (x : ℕ) < 4 := by
      simp only [PairHS.bs, List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    rw [← hrep x x.2]
    exact h3 x hx4
  apply h4
  rw [hrep _ h2, h1']
  rfl

theorem mul_memP_iff {x y : Equiv.Perm (Fin 3850)} (hx : x ∈ hsR) (hy : y ∈ hsR) :
    x * y ∈ hsP ↔ (x ∈ hsP ↔ y ∈ hsP) := by
  by_cases hxP : x ∈ hsP
  · simp only [hxP, true_iff]
    exact ⟨fun h => by simpa using hsP.mul_mem (hsP.inv_mem hxP) h, fun h => hsP.mul_mem hxP h⟩
  · simp only [hxP, false_iff]
    constructor
    · intro h hyP
      exact hxP (by simpa using hsP.mul_mem h (hsP.inv_mem hyP))
    · intro hyP
      have hxu : x * hsU ∈ hsP := (HS72.memR.1 hx).resolve_left hxP
      have hyu : y * hsU ∈ hsP := (HS72.memR.1 hy).resolve_left hyP
      have huy : hsU * y ∈ hsP := by
        have := HS72.U_conj _ hyu
        rwa [HS72.U_inv, mul_assoc, mul_assoc, HS72.U_sq, mul_one] at this
      have e1 : x * y = (x * hsU) * (hsU * y) := by
        rw [mul_assoc, ← mul_assoc hsU, HS72.U_sq, one_mul]
      rw [e1]
      exact hsP.mul_mem hxu huy

theorem bit6 {l : ℕ} (hl : l < 4) :
    (bitB 6 l = true ↔ Nat.land (Nat.shiftRight 6 l) 1 ≠ 0) := by
  interval_cases l <;> decide

theorem sg_mem_iff {l : ℕ} (hl : l < 4) :
    sg l ∈ hsP ↔ Nat.land (Nat.shiftRight (GO 0) l) 1 = 0 := by
  have h := c_cos
  rw [andB_iff, beq_iff, allN_iff] at h
  obtain ⟨hgo, hc⟩ := h
  have hl' := hc l hl
  unfold cosAt at hl'
  rw [letB_eq, andB_iff] at hl'
  obtain ⟨hw, h5⟩ := hl'
  rw [hgo]
  have hsR' := HS72.S_le_R (sg_memS hl)
  have hwR := HS72.P_le_R (wA_memP hw)
  cases hb : bitB 6 l
  · have hb' : Nat.land (Nat.shiftRight 6 l) 1 = 0 := by
      by_contra hne
      exact absurd ((bit6 hl).2 hne) (by rw [hb]; decide)
    simp only [hb', iff_true]
    have e1 : (fun x => letN (evW evH (KW l) x) fun y =>
        Bool.rec (motive := fun _ => ℕ) y (evH (HZ 0) y) (bitB (GO 0) l)) = evW evH (KW l) := by
      funext x
      rw [letN_eq, hgo, hb]
    rw [e1] at h5
    rw [eqR5 (sg_rep hl) (wA_rep hw) hsR' hwR h5]
    exact wA_memP hw
  · have hb' : Nat.land (Nat.shiftRight 6 l) 1 ≠ 0 := (bit6 hl).1 hb
    simp only [hb', iff_false]
    have e1 : (fun x => letN (evW evH (KW l) x) fun y =>
        Bool.rec (motive := fun _ => ℕ) y (evH (HZ 0) y) (bitB (GO 0) l)) =
        fun x => evH (HZ 0) (evW evH (KW l) x) := by
      funext x
      rw [letN_eq, hgo, hb]
    rw [e1] at h5
    have hz := z_parts.1
    have hrep := (evH_small hz).comp (wA_rep hw)
    have heq := eqR5 (sg_rep hl) hrep hsR' (hsR.mul_mem (e_memR hz) hwR) h5
    intro hP
    apply ez_notMem
    have : e (HZ 0) = sg l * (wA (KW l))⁻¹ := by rw [heq, mul_inv_cancel_right]
    rw [this]
    exact hsP.mul_mem hP (hsP.inv_mem (wA_memP hw))

theorem e_mem_iff {k : ℕ} (hk : k < 1024) : e k ∈ hsP ↔ parK SPA (GO 0) 9 k = 0 :=
  parK_mem tree' (fun l hl => HS72.S_le_R (sg_memS hl))
    (fun x hx y hy => mul_memP_iff hx hy) (fun l hl => sg_mem_iff hl) 9 k hk
    (parK_lt_of_dep _ 9 k (dep hk))

end HS4

end CFSG.KD.HS119

end
