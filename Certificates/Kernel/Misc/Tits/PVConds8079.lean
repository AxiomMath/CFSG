module

public import Certificates.Kernel.Misc.Tits.PTable8079
public import Certificates.Kernel.Misc.Tits.JVConds8073

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.PV

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN CertificateChecks.KernelMisc.TitsJT CFSG.KS.Bfs
open CertificateChecks.KernelMisc.TitsJT.V (X pt onB sJ sJ_rep sJ_mem mem_SJ SJ X_eq pt_eq finPt_coe
  onB_iff Z_rep cc_norm Bc bI bI_lt bcg bcg_zero bcg_succ bcg_mem Bc_rep memN memN_iff allL_iff' LAM
  EIX INV cls WD spanF appL_eq xorL_eq spanF_cons enc gw)
open scoped commutatorElement

theorem bIf_t {c t e : Bool} (h : c = true) : bIf(c, t, e) = t := by subst h; rfl

theorem bIf_f {c t e : Bool} (h : c = false) : bIf(c, t, e) = e := by subst h; rfl

theorem notB {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

theorem eqB {c s : Bool}
    (h : Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false s) s c =
      true) : c = s := by
  cases c <;> cases s
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

theorem test2_spec {i cl : ℕ} (h : test2 i cl = true) :
    (Nat.blt i 512 = true → memN (lmP 0 i) LAM = true) ∧
    (Nat.blt i 512 = false → isOneP i = false) ∧
    (PbP i = true → Nat.blt i 512 = true ∧ Nat.beq cl 0 = true ∧ cmP i Pi = true ∧
      sqP i = true ∧ Nat.beq (lmP 0 i) 0 = true ∧ (allcP i = true → isOneP i = true ∨ isZP i = true)) ∧
    (PbP i = false → Nat.beq cl 0 = false ∧
      (Nat.beq (lmP 0 i) 0 = true → Nat.beq cl 3 = true ∧ sqP i = false) ∧
      (Nat.beq (lmP 0 i) 0 = false → Nat.beq cl 3 = false ∧
        Nat.beq (lamP 4 i) (lamP 0 i) = false ∧ coverP i = true ∧ Nat.beq cl 1 = sqP i)) := by
  unfold test2 at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨fun hb => ?_, fun hb => ?_, fun hP => ?_, fun hP => ?_⟩
  · rw [bIf_t hb] at h1
    exact h1
  · rw [bIf_f hb] at h1
    exact notB h1
  · rw [bIf_t hP] at h2
    obtain ⟨a, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    obtain ⟨b, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    obtain ⟨c, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    obtain ⟨d, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    obtain ⟨e, f⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    refine ⟨a, b, c, d, e, fun hc => ?_⟩
    rw [bIf_t hc] at f
    cases hO : isOneP i
    · rw [bIf_f hO] at f
      exact Or.inr f
    · exact Or.inl rfl
  · rw [bIf_f hP] at h2
    obtain ⟨a, b⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    refine ⟨notB a, fun hl => ?_, fun hl => ?_⟩
    · rw [bIf_t hl] at b
      obtain ⟨c, d⟩ := (CFSG.KS.bAnd_iff _ _).1 b
      exact ⟨c, notB d⟩
    · rw [bIf_f hl] at b
      obtain ⟨c, b⟩ := (CFSG.KS.bAnd_iff _ _).1 b
      obtain ⟨d, b⟩ := (CFSG.KS.bAnd_iff _ _).1 b
      obtain ⟨e, f⟩ := (CFSG.KS.bAnd_iff _ _).1 b
      exact ⟨notB c, notB d, e, eqB f⟩

theorem cls_vals (i : ℕ) : cls i = 0 ∨ cls i = 1 ∨ cls i = 2 := by
  unfold V.cls
  generalize memN i EIX = a
  generalize memN i INV = b
  cases a <;> cases b <;> decide

theorem clsP_lo {i : ℕ} (hi : i < 512) : clsP i = cls i := by
  unfold clsP
  rw [blt_lo hi]

theorem clsP_hi {i : ℕ} (hi : ¬ i < 512) : clsP i = 2 ∨ (clsP i = 3 ∧ memN (i - 512) EIX = true) := by
  unfold clsP
  rw [blt_hi hi]
  change nIf(memN (i - 512) EIX, 3, 2) = 2 ∨ (nIf(memN (i - 512) EIX, 3, 2) = 3 ∧ _)
  generalize memN (i - 512) EIX = a
  cases a
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩

theorem clsP3 {i : ℕ} (h : clsP i = 3) : ¬ i < 512 ∧ memN (i - 512) EIX = true := by
  by_cases hi : i < 512
  · rw [clsP_lo hi] at h
    rcases cls_vals i with e | e | e <;> omega
  · rcases clsP_hi hi with e | e
    · omega
    · exact ⟨hi, e.2⟩

theorem clsP1 {i : ℕ} (h : clsP i = 1) : i < 512 ∧ cls i = 1 := by
  by_cases hi : i < 512
  · rw [clsP_lo hi] at h
    exact ⟨hi, h⟩
  · rcases clsP_hi hi with e | e <;> omega

theorem cls_EIX {j : ℕ} (h : memN j EIX = true) : cls j = 0 := by
  unfold V.cls
  rw [h]

theorem PbP_of_cls0 {i : ℕ} (hi : i < 1024) (h : clsP i = 0) : PbP i = true := by
  cases e : PbP i
  · have := ((test2_spec (tst2 hi)).2.2.2 e).1
    rw [h] at this
    exact absurd this (by decide)
  · rfl

variable (hπ : PiHyp)
include hπ

omit hπ in
theorem fv1 {n : ℕ} (h : n < 1024) : ((finPt 1024 n : Fin 1024) : ℕ) = n := finPt_val h

omit hπ in
theorem elPF_inj {i j : Fin 1024} (h : elP i = elP j) : i = j := Fin.ext (elP_inj i.2 j.2 h)

theorem mul_valP (i j : Fin 1024) : (pOps.mul i j : ℕ) = (pMulT[(i : ℕ)]!)[(j : ℕ)]! :=
  fv1 (mulTP hπ i.2 j.2).1

theorem el_mulP (i j : Fin 1024) : elP (pOps.mul i j) = elP i * elP j := by
  rw [mul_valP hπ]
  exact (mulTP hπ i.2 j.2).2

theorem el_invP (i : Fin 1024) : elP (pOps.inv i) = (elP i)⁻¹ := by
  have e : (pOps.inv i : ℕ) = pInvT[(i : ℕ)]! := fv1 (invTP hπ i.2).1
  rw [e]
  exact (invTP hπ i.2).2

theorem one_valP : (pOps.one : ℕ) = pOneI := fv1 (oneTP hπ).1

theorem el_oneP : elP pOps.one = 1 := by
  rw [one_valP hπ]
  exact (oneTP hπ).2

theorem el_zP : elP pOps.zI = titsZ := by
  have e : (pOps.zI : ℕ) = pZI := fv1 (zTP hπ).1
  rw [e]
  exact (zTP hπ).2

theorem el_ccP (i : Fin 1024) : elP (pCc i) = cc * elP i * cc⁻¹ := by
  have e : (pCc i : ℕ) = pCcT[(i : ℕ)]! := fv1 (ccTP hπ i.2).1
  rw [e]
  exact (ccTP hπ i.2).2

theorem cj_valP (k : Fin 4) (i : Fin 1024) : (pCj k i : ℕ) = (pCjT[(k : ℕ)]!)[(i : ℕ)]! :=
  fv1 (cjTP hπ k.2 i.2).1

theorem el_commP (i j : Fin 1024) : elP (pOps.comm i j) = ⁅elP i, elP j⁆ := by
  simp only [VOps.comm, el_mulP hπ, el_invP hπ, commutatorElement_def]

theorem elPF_mem (i : Fin 1024) : elP i ∈ Psub hπ := elP_mem hπ i.2

theorem elPF_surj {g : Equiv.Perm (Fin 1755)} (hg : g ∈ Psub hπ) : ∃ i : Fin 1024, elP i = g := by
  obtain ⟨i, hi, e⟩ := elP_surj hπ hg
  exact ⟨⟨i, hi⟩, e⟩

theorem onBP_eq_iff {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ Psub hπ) (hb : b ∈ Psub hπ)
    {fa fb : ℕ → ℕ} (hfa : ∀ p < 1755, fa p = a (finPt 1755 p))
    (hfb : ∀ p < 1755, fb p = b (finPt 1755 p)) :
    onB (fun p => Nat.beq (fa p) (fb p)) = true ↔ a = b := by
  rw [onB_iff]
  constructor
  · intro h
    refine agreeP hπ ha hb fun p hp => ?_
    have := h p hp
    rwa [Nat.beq_eq, hfa p (base_lt hp), hfb p (base_lt hp)] at this
  · rintro rfl p hp
    rw [Nat.beq_eq, hfa p (base_lt hp), hfb p (base_lt hp)]

omit hπ in
theorem XP_g {i : ℕ} (hi : i < 1024) {P : ℕ} {g : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 (unpack 1755 11 P) g) {p : ℕ} (hp : p < 1755) :
    XP i (pt P p) = ((elP i * g) (finPt 1755 p) : ℕ) := by
  rw [pt_eq hr hp, XP_eq hi (g _).2, finPt_coe, Equiv.Perm.mul_apply]

omit hπ in
theorem g_XP {i : ℕ} (hi : i < 1024) {P : ℕ} {g : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 (unpack 1755 11 P) g) {p : ℕ} (hp : p < 1755) :
    pt P (XP i p) = ((g * elP i) (finPt 1755 p) : ℕ) := by
  rw [XP_eq hi hp, pt_eq hr (elP i _).2, finPt_coe, Equiv.Perm.mul_apply]

theorem cmP_iff {i : ℕ} (hi : i < 1024) {P : ℕ} {g : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 (unpack 1755 11 P) g) (hg : g ∈ Psub hπ) :
    cmP i P = true ↔ Commute (elP i) g := by
  unfold cmP
  exact onBP_eq_iff hπ (fa := fun p => XP i (pt P p)) (fb := fun p => pt P (XP i p))
    (mul_mem (elP_mem hπ hi) hg) (mul_mem hg (elP_mem hπ hi)) (fun p hp => XP_g hi hr hp)
    (fun p hp => g_XP hi hr hp)

theorem zcP_iff {i : ℕ} (hi : i < 1024) {P : ℕ} {g : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 (unpack 1755 11 P) g) (hg : g ∈ Psub hπ) :
    zcP i P = true ↔ elP i * g = titsZ * g * elP i := by
  unfold zcP
  refine onBP_eq_iff hπ (fa := fun p => XP i (pt P p)) (fb := fun p => pt Z (pt P (XP i p)))
    (mul_mem (elP_mem hπ hi) hg) (mul_mem (mul_mem (J_le hπ z_mem) hg) (elP_mem hπ hi))
    (fun p hp => XP_g hi hr hp) (fun p hp => ?_)
  calc pt Z (pt P (XP i p)) = pt Z ((g * elP i) (finPt 1755 p) : ℕ) :=
        congrArg (pt Z) (g_XP hi hr hp)
    _ = (titsZ (finPt 1755 ((g * elP i) (finPt 1755 p) : ℕ)) : ℕ) :=
        pt_eq Z_rep (((g * elP i) (finPt 1755 p)).2)
    _ = ((titsZ * g * elP i) (finPt 1755 p) : ℕ) := by
        rw [finPt_coe, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem sqP_iff {i : ℕ} (hi : i < 1024) : sqP i = true ↔ elP i * elP i = 1 := by
  unfold sqP
  exact onBP_eq_iff hπ (fa := fun p => XP i (XP i p)) (fb := fun p => p)
    (mul_mem (elP_mem hπ hi) (elP_mem hπ hi)) (one_mem _)
    (fun p hp => (congrArg (XP i) (XP_eq hi hp)).trans ((XP_eq hi (elP i _).2).trans (by
      rw [finPt_coe, Equiv.Perm.mul_apply])))
    (fun p hp => by rw [Equiv.Perm.one_apply, finPt_val hp])

theorem oneP_iff {i : ℕ} (hi : i < 1024) : isOneP i = true ↔ elP i = 1 := by
  unfold isOneP
  exact onBP_eq_iff hπ (fa := fun p => XP i p) (fb := fun p => p) (elP_mem hπ hi) (one_mem _)
    (fun p hp => XP_eq hi hp) (fun p hp => by rw [Equiv.Perm.one_apply, finPt_val hp])

theorem zP_iff {i : ℕ} (hi : i < 1024) : isZP i = true ↔ elP i = titsZ := by
  unfold isZP
  exact onBP_eq_iff hπ (fa := fun p => XP i p) (fb := fun p => pt Z p) (elP_mem hπ hi)
    (J_le hπ z_mem) (fun p hp => XP_eq hi hp) (fun p hp => pt_eq Z_rep hp)

omit hπ in
@[expose] def SP : Set (Equiv.Perm (Fin 1755)) := SJ ∪ {piP}

theorem closure_SP : Subgroup.closure SP = Psub hπ := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro s (hs | hs)
    · exact J_le hπ (Subgroup.subset_closure hs)
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact pi_mem hπ
  · have hJ : titsJ ≤ Subgroup.closure SP := by
      rw [← V.closure_SJ]
      exact Subgroup.closure_mono Set.subset_union_left
    have hpi : piP ∈ Subgroup.closure SP :=
      Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton _))
    rintro x (hx | hx)
    · exact hJ hx
    · have := mul_mem (hJ hx) hpi
      rwa [inv_mul_cancel_right] at this

theorem mem_cl {x : Equiv.Perm (Fin 1755)} (hx : x ∈ Psub hπ) : x ∈ Subgroup.closure SP := by
  rw [closure_SP hπ]
  exact hx

omit hπ in
theorem el2 : elP 2 = titsZ := by
  rw [elP_lo (i := 2) (by norm_num)]
  exact (V.z_iff (by norm_num)).1 z2

omit hπ in
theorem clsP_two : clsP 2 = 0 := by decide

theorem z_pi : Commute titsZ piP := by
  have hP := PbP_of_cls0 (by norm_num) clsP_two
  have hc := ((test2_spec (tst2 (i := 2) (by norm_num))).2.2.1 hP).2.2.1
  have := (cmP_iff hπ (by norm_num) piP_rep (pi_mem hπ)).1 hc
  rwa [el2] at this

theorem zFactsP : (∀ y ∈ Subgroup.closure SP, Commute titsZ y) ∧ titsZ * titsZ = 1 ∧ titsZ ≠ 1 := by
  refine ⟨fun y hy => ?_, V.zFacts.2.1, V.zFacts.2.2⟩
  induction hy using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with hs | hs
    · exact V.zFacts.1 s (Subgroup.subset_closure hs)
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact z_pi hπ
  | one => exact Commute.one_right _
  | mul y w _ _ py pw => exact py.mul_right pw
  | inv y _ py => exact py.inv_right

@[expose] noncomputable def Esp : Subgroup (Equiv.Perm (Fin 1755)) :=
  Grp.eSub (zFactsP hπ).1 (zFactsP hπ).2.1

theorem Esp_le {x : Equiv.Perm (Fin 1755)} (hx : x ∈ Esp hπ) : x ∈ Psub hπ := by
  rw [← closure_SP hπ]
  exact hx.1

theorem pk_iff {i : ℕ} (hi : i < 1024) {k : ℕ} (hk : k < 4) :
    (bIf(cmP i (TitsJ.S k), true, zcP i (TitsJ.S k))) = true ↔ Grp.Z0 titsZ ⁅elP i, sJ k⁆ := by
  have hs := J_le hπ (sJ_mem hk)
  rw [Grp.Z0, commutatorElement_eq_one_iff_commute, ← cmP_iff hπ hi (sJ_rep hk) hs]
  have e2 : ⁅elP i, sJ k⁆ = titsZ ↔ zcP i (TitsJ.S k) = true := by
    rw [zcP_iff hπ hi (sJ_rep hk) hs, commutatorElement_def]
    constructor
    · intro h
      rw [← h]
      group
    · intro h
      rw [h]
      group
  rw [e2]
  cases cmP i (TitsJ.S k) <;> simp

theorem PbP_iff {i : ℕ} (hi : i < 1024) : PbP i = true ↔ elP i ∈ Esp hπ := by
  rw [Esp, Grp.mem_eSub_iff _ _ (mem_cl hπ (elP_mem hπ hi))]
  constructor
  · intro h s hs
    rcases hs with hs | hs
    · obtain ⟨k, hk, rfl⟩ := mem_SJ.1 hs
      exact (pk_iff hπ hi hk).1 (allN_spec h k hk)
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      have hc := ((test2_spec (tst2 hi)).2.2.1 h).2.2.1
      left
      rw [commutatorElement_eq_one_iff_commute]
      exact (cmP_iff hπ hi piP_rep (pi_mem hπ)).1 hc
  · intro h
    exact allN_of_forall fun k hk => (pk_iff hπ hi hk).2 (h _ (Or.inl (mem_SJ.2 ⟨k, hk, rfl⟩)))

theorem Esp_sq {e : Equiv.Perm (Fin 1755)} (he : e ∈ Esp hπ) : e * e = 1 := by
  obtain ⟨i, hi, rfl⟩ := elP_surj hπ (Esp_le hπ he)
  exact (sqP_iff hπ hi).1 ((test2_spec (tst2 hi)).2.2.1 ((PbP_iff hπ hi).2 he)).2.2.2.1

theorem Esp_comm {e e' : Equiv.Perm (Fin 1755)} (he : e ∈ Esp hπ) (he' : e' ∈ Esp hπ) :
    Commute e e' := Grp.commute_of_sq (fun _ he => Esp_sq hπ he) he he'

theorem pi_comm {e : Equiv.Perm (Fin 1755)} (he : e ∈ Esp hπ) : Commute e piP := by
  obtain ⟨i, hi, rfl⟩ := elP_surj hπ (Esp_le hπ he)
  have hc := ((test2_spec (tst2 hi)).2.2.1 ((PbP_iff hπ hi).2 he)).2.2.1
  exact (cmP_iff hπ hi piP_rep (pi_mem hπ)).1 hc

theorem bm_memP {m : ℕ} (hm : m < 5) : el (bI m) ∈ Esp hπ := by
  have hb := bI_lt hm
  rw [← elP_lo hb]
  refine (PbP_iff hπ (by omega)).1 (PbP_of_cls0 (by omega) ?_)
  rw [clsP_lo hb]
  interval_cases m <;> decide

omit hπ in
theorem pEB_eq (i : Fin 1024) :
    pEB i = true ↔ ∀ j : Fin 1024, pOps.comm i j = pOps.one ∨ pOps.comm i j = pOps.zI := by
  unfold pEB pEBarr
  rw [getElem!_ofFn_of_lt _ i.2]
  exact decide_eq_true_iff

omit hπ in
theorem pFB_eq (i : Fin 1024) :
    pFB i = true ↔ ∀ e : Fin 1024, pEB e = true → pOps.mul i e = pOps.mul e i := by
  unfold pFB pFBarr
  rw [getElem!_ofFn_of_lt _ i.2]
  exact decide_eq_true_iff

theorem pEB_iff (i : Fin 1024) : pEB i = true ↔ elP i ∈ Esp hπ := by
  rw [pEB_eq]
  constructor
  · intro h
    refine ⟨mem_cl hπ (elPF_mem hπ i), fun y hy => ?_⟩
    rw [closure_SP hπ] at hy
    obtain ⟨j, rfl⟩ := elPF_surj hπ hy
    rcases h j with e | e
    · left
      rw [← el_commP hπ, e, el_oneP hπ]
    · right
      rw [← el_commP hπ, e, el_zP hπ]
  · rintro ⟨-, h⟩ j
    rcases h (elP j) (mem_cl hπ (elPF_mem hπ j)) with e | e
    · left
      exact elPF_inj (by rw [el_commP hπ, el_oneP hπ, e])
    · right
      exact elPF_inj (by rw [el_commP hπ, el_zP hπ, e])

theorem pFB_iff (i : Fin 1024) : pFB i = true ↔ ∀ e ∈ Esp hπ, Commute (elP i) e := by
  rw [pFB_eq]
  constructor
  · intro h e he
    obtain ⟨k, rfl⟩ := elPF_surj hπ (Esp_le hπ he)
    have := h k ((pEB_iff hπ k).2 he)
    unfold Commute SemiconjBy
    rw [← el_mulP hπ, ← el_mulP hπ, this]
  · intro h e he
    exact elPF_inj (by rw [el_mulP hπ, el_mulP hπ]; exact h _ ((pEB_iff hπ e).1 he))

theorem pEB_PbP (i : Fin 1024) : pEB i = PbP i := by
  refine Bool.eq_iff_iff.2 ?_
  rw [pEB_iff hπ, PbP_iff hπ i.2]

omit hπ in
@[expose] def enc6 (b0 b1 b2 b3 b4 b5 : Bool) : ℕ :=
  Nat.add (enc b0 b1 b2 b3 b4) (Bool.rec (motive := fun _ => Nat) 32 0 b5)

local instance decForallBool {p : Bool → Prop} [DecidablePred p] : Decidable (∀ b, p b) :=
  decidable_of_iff (p false ∧ p true)
    ⟨fun ⟨h1, h2⟩ b => by cases b <;> assumption, fun h => ⟨h _, h _⟩⟩

omit hπ in
theorem enc6_bit (b0 b1 b2 b3 b4 b5 : Bool) : enc6 b0 b1 b2 b3 b4 b5 < 64 ∧
    (enc6 b0 b1 b2 b3 b4 b5).testBit 0 = !b0 ∧ (enc6 b0 b1 b2 b3 b4 b5).testBit 1 = !b1 ∧
    (enc6 b0 b1 b2 b3 b4 b5).testBit 2 = !b2 ∧ (enc6 b0 b1 b2 b3 b4 b5).testBit 3 = !b3 ∧
    (enc6 b0 b1 b2 b3 b4 b5).testBit 4 = !b4 ∧ (enc6 b0 b1 b2 b3 b4 b5).testBit 5 = !b5 := by
  revert b0 b1 b2 b3 b4 b5
  decide

omit hπ in
theorem lamP_eq (j i : ℕ) : lamP j i = enc6 (cmP i (Bc j 0)) (cmP i (Bc j 1)) (cmP i (Bc j 2))
    (cmP i (Bc j 3)) (cmP i (Bc j 4)) (Nat.blt i 512) := rfl

omit hπ in
theorem lmP_eq (j i : ℕ) : lmP j i = enc (cmP i (Bc j 0)) (cmP i (Bc j 1)) (cmP i (Bc j 2))
    (cmP i (Bc j 3)) (cmP i (Bc j 4)) := rfl

omit hπ in
theorem lamP_lt (j i : ℕ) : lamP j i < 64 := by
  rw [lamP_eq]
  exact (enc6_bit _ _ _ _ _ _).1

omit hπ in
theorem lamP_bit (j i : ℕ) {m : ℕ} (hm : m < 5) : (lamP j i).testBit m = !(cmP i (Bc j m)) := by
  rw [lamP_eq]
  obtain ⟨-, h0, h1, h2, h3, h4, -⟩ := enc6_bit (cmP i (Bc j 0)) (cmP i (Bc j 1)) (cmP i (Bc j 2))
    (cmP i (Bc j 3)) (cmP i (Bc j 4)) (Nat.blt i 512)
  interval_cases m
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

omit hπ in
theorem lamP_bit5 (j i : ℕ) : (lamP j i).testBit 5 = !(Nat.blt i 512) := by
  rw [lamP_eq]
  exact (enc6_bit _ _ _ _ _ _).2.2.2.2.2.2

omit hπ in
theorem lamP_lo {j i : ℕ} (hi : i < 512) : lamP j i = lmP j i := by
  unfold lamP
  rw [blt_lo hi]
  exact Nat.add_zero _

omit hπ in
theorem lamP_hi {j i : ℕ} (hi : ¬ i < 512) : lamP j i = lmP j i + 32 := by
  unfold lamP
  rw [blt_hi hi]
  rfl

omit hπ in
theorem bits_eq6 {v w : ℕ} (hv : v < 64) (hw : w < 64) (h : ∀ m < 6, v.testBit m = w.testBit m) :
    v = w := by
  refine Nat.eq_of_testBit_eq fun m => ?_
  by_cases hm : m < 6
  · exact h m hm
  · have h64 : (64 : ℕ) ≤ 2 ^ m := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv h64), Nat.testBit_lt_two_pow (lt_of_lt_of_le hw h64)]

theorem cmP_bc {i : ℕ} (hi : i < 1024) {j m : ℕ} (hj : j < 5) (hm : m < 5) :
    cmP i (Bc j m) = true ↔ Commute (elP i) (bcg j m) :=
  cmP_iff hπ hi (Bc_rep hm j hj) (J_le hπ (bcg_mem hm j))

open scoped Classical in
theorem lamP0_bit {i : ℕ} (hi : i < 1024) {m : ℕ} (hm : m < 5) :
    (lamP 0 i).testBit m = decide (¬ Commute (el (bI m)) (elP i)) := by
  rw [lamP_bit 0 i hm, V.bool_not_of_iff (cmP_bc hπ hi (by omega) hm), bcg_zero]
  simp only [Commute.symm_iff (a := elP i)]

omit hπ in
open scoped Classical in
theorem lamP_bit5' (j : ℕ) {i : ℕ} (hi : i < 1024) :
    (lamP j i).testBit 5 = decide (elP i ∉ titsJ) := by
  rw [lamP_bit5]
  by_cases h : i < 512
  · rw [blt_lo h]
    simp [(elP_J_iff hi).2 h]
  · rw [blt_hi h]
    have : elP i ∉ titsJ := fun h' => h ((elP_J_iff hi).1 h')
    simp [this]

theorem coset_mul {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ Psub hπ) (hb : b ∈ Psub hπ) :
    a * b ∈ titsJ ↔ (a ∈ titsJ ↔ b ∈ titsJ) := by
  by_cases p : a ∈ titsJ <;> by_cases q : b ∈ titsJ
  · exact iff_of_true (mul_mem p q) (iff_of_true p q)
  · refine iff_of_false (fun h => q ?_) (fun h => q (h.1 p))
    have := mul_mem (inv_mem p) h
    rwa [inv_mul_cancel_left] at this
  · refine iff_of_false (fun h => p ?_) (fun h => p (h.2 q))
    have := mul_mem h (inv_mem q)
    rwa [mul_inv_cancel_right] at this
  · refine iff_of_true ?_ (iff_of_false p q)
    have ha' : a * piP⁻¹ ∈ titsJ := ha.resolve_left p
    have hb' : b * piP⁻¹ ∈ titsJ := hb.resolve_left q
    have e : a * b = (a * piP⁻¹) * (piP * (b * piP⁻¹) * piP⁻¹) * (piP * piP) := by group
    rw [e]
    exact mul_mem (mul_mem ha' (piJ hπ hb')) hπ.sq

theorem lamP0_mul {a b x : ℕ} (ha : a < 1024) (hb : b < 1024) (hx : x < 1024)
    (h : elP x = elP a * elP b) : lamP 0 x = lamP 0 a ^^^ lamP 0 b := by
  refine bits_eq6 (lamP_lt 0 x) (Nat.xor_lt_two_pow (n := 6) (lamP_lt 0 a) (lamP_lt 0 b))
    fun m hm => ?_
  rw [Nat.testBit_xor]
  by_cases h5 : m = 5
  · subst h5
    rw [lamP_bit5' 0 hx, lamP_bit5' 0 ha, lamP_bit5' 0 hb, h,
      coset_mul hπ (elP_mem hπ ha) (elP_mem hπ hb)]
    by_cases p : elP a ∈ titsJ <;> by_cases q : elP b ∈ titsJ <;> simp [p, q]
  · have hm5 : m < 5 := by omega
    rw [lamP0_bit hπ hx hm5, lamP0_bit hπ ha hm5, lamP0_bit hπ hb hm5, h,
      Grp.comm_mul_iff (zFactsP hπ).1 (zFactsP hπ).2.1 (zFactsP hπ).2.2 (bm_memP hπ hm5)
        (mem_cl hπ (elP_mem hπ ha)) (mem_cl hπ (elP_mem hπ hb))]
    by_cases p : Commute (el (bI m)) (elP a) <;> by_cases q : Commute (el (bI m)) (elP b) <;>
      simp [p, q]

theorem lamP0_inv {a x : ℕ} (ha : a < 1024) (hx : x < 1024) (h : elP x = (elP a)⁻¹) :
    lamP 0 x = lamP 0 a := by
  refine bits_eq6 (lamP_lt 0 x) (lamP_lt 0 a) fun m hm => ?_
  by_cases h5 : m = 5
  · subst h5
    rw [lamP_bit5' 0 hx, lamP_bit5' 0 ha, h, inv_mem_iff]
  · rw [lamP0_bit hπ hx (by omega), lamP0_bit hπ ha (by omega), h, Commute.inv_right_iff]

theorem lamP0_mulF (w y : Fin 1024) : lamP 0 (pOps.mul w y) = lamP 0 w ^^^ lamP 0 y :=
  lamP0_mul hπ w.2 y.2 (Fin.is_lt _) (el_mulP hπ w y)

theorem lamP0_invF (w : Fin 1024) : lamP 0 (pOps.inv w) = lamP 0 w :=
  lamP0_inv hπ w.2 (Fin.is_lt _) (el_invP hπ w)

theorem lamP0_oneF : lamP 0 pOps.one = 0 := by
  have h1 : (pOps.one : ℕ) < 512 := (elP_J_iff (Fin.is_lt _)).1 (by rw [el_oneP hπ]; exact one_mem _)
  refine bits_eq6 (lamP_lt 0 _) (by norm_num) fun m hm => ?_
  rw [Nat.zero_testBit]
  by_cases h5 : m = 5
  · subst h5
    rw [lamP_bit5, blt_lo h1]
    rfl
  · rw [lamP0_bit hπ (Fin.is_lt _) (by omega), el_oneP hπ]
    simp [Commute.one_right]

omit hπ in
theorem lamP0_zero {x : ℕ} (h : lamP 0 x = 0) : x < 512 ∧ lmP 0 x = 0 := by
  by_cases hx : x < 512
  · rw [lamP_lo hx] at h
    exact ⟨hx, h⟩
  · rw [lamP_hi hx] at h
    omega

theorem pFB_lam (i : Fin 1024) : pFB i = true ↔ Nat.beq (lmP 0 i) 0 = true := by
  rw [pFB_iff hπ]
  constructor
  · intro h
    have hc : ∀ m < 5, cmP i (Bc 0 m) = true := fun m hm => by
      rw [cmP_bc hπ i.2 (by omega) hm, bcg_zero]
      exact h _ (bm_memP hπ hm)
    rw [lmP_eq, hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega), hc 4 (by omega)]
    rfl
  · intro hl e he
    have spec := test2_spec (tst2 i.2)
    cases hP : PbP i
    · obtain ⟨h3, -⟩ := (spec.2.2.2 hP).2.1 hl
      obtain ⟨hlo, hE⟩ := clsP3 (Nat.eq_of_beq_eq_true h3)
      have hk : i.val - 512 < 1024 := by omega
      have hb : elP (i.val - 512) ∈ Esp hπ :=
        (PbP_iff hπ hk).1 (PbP_of_cls0 hk (by rw [clsP_lo (by omega)]; exact cls_EIX hE))
      rw [elP_hi hlo, ← elP_lo (i := i.val - 512) (by omega)]
      exact (Esp_comm hπ hb he).mul_left (pi_comm hπ he).symm
    · exact Esp_comm hπ ((PbP_iff hπ i.2).1 hP) he

theorem pFB_cls (i : Fin 1024) :
    pFB i = true ↔ (Nat.beq (clsP i) 0 = true ∨ Nat.beq (clsP i) 3 = true) := by
  rw [pFB_lam hπ]
  have spec := test2_spec (tst2 i.2)
  cases hP : PbP i
  · obtain ⟨h0, s1, s2⟩ := spec.2.2.2 hP
    cases hl : Nat.beq (lmP 0 i) 0
    · obtain ⟨h3, -⟩ := s2 hl
      rw [h0, h3]
      exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by
        rcases h with h | h <;> exact absurd h Bool.false_ne_true⟩
    · exact ⟨fun _ => Or.inr (s1 hl).1, fun _ => rfl⟩
  · obtain ⟨-, h0, -, -, hl, -⟩ := spec.2.2.1 hP
    exact ⟨fun _ => Or.inl h0, fun _ => hl⟩

theorem pEB_cls (i : Fin 1024) : pEB i = true ↔ Nat.beq (clsP i) 0 = true := by
  rw [pEB_PbP hπ]
  have spec := test2_spec (tst2 i.2)
  cases hP : PbP i
  · rw [(spec.2.2.2 hP).1]
  · rw [(spec.2.2.1 hP).2.1]

omit hπ in
theorem vA2 : VCondsA pOps pEB pFB := ⟨pEB_eq, pFB_eq⟩

theorem vB2 : VCondsB pOps pEB pFB := by
  refine ⟨fun i j hi hj => ?_, fun i hi => ?_, ?_, fun i j hi hj => ?_, fun i hi => ?_, ?_⟩
  · rw [pEB_iff hπ, el_mulP hπ]
    exact (Esp hπ).mul_mem ((pEB_iff hπ i).1 hi) ((pEB_iff hπ j).1 hj)
  · rw [pEB_iff hπ, el_invP hπ]
    exact (Esp hπ).inv_mem ((pEB_iff hπ i).1 hi)
  · rw [pEB_iff hπ, el_oneP hπ]
    exact (Esp hπ).one_mem
  · rw [pFB_iff hπ, el_mulP hπ]
    exact fun e he => ((pFB_iff hπ i).1 hi e he).mul_left ((pFB_iff hπ j).1 hj e he)
  · rw [pFB_iff hπ, el_invP hπ]
    exact fun e he => ((pFB_iff hπ i).1 hi e he).inv_left
  · rw [pFB_iff hπ, el_oneP hπ]
    exact fun e _ => Commute.one_left e

omit hπ in
theorem card_cls0 : (Finset.univ.filter fun i : Fin 1024 => Nat.beq (clsP i) 0 = true).card = 32 := by
  decide +kernel

omit hπ in
theorem card_cls03 : (Finset.univ.filter fun i : Fin 1024 =>
    (Nat.beq (clsP i) 0 = true ∨ Nat.beq (clsP i) 3 = true)).card = 64 := by
  decide +kernel

theorem vC2 : VCondsC pOps pEB pFB := by
  have hF : (Finset.univ.filter fun i : Fin 1024 => pFB i = true) =
      Finset.univ.filter fun i : Fin 1024 =>
        (Nat.beq (clsP i) 0 = true ∨ Nat.beq (clsP i) 3 = true) :=
    Finset.filter_congr fun i _ => pFB_cls hπ i
  have hE : (Finset.univ.filter fun i : Fin 1024 => pEB i = true) =
      Finset.univ.filter fun i : Fin 1024 => Nat.beq (clsP i) 0 = true :=
    Finset.filter_congr fun i _ => pEB_cls hπ i
  refine ⟨fun e he => ?_, fun e e' he he' => ?_, ?_, ?_, fun e he hc => ?_, fun i j => ?_⟩
  · exact elPF_inj (by rw [el_mulP hπ, el_oneP hπ]; exact Esp_sq hπ ((pEB_iff hπ e).1 he))
  · exact elPF_inj (by
      rw [el_mulP hπ, el_mulP hπ]
      exact (Esp_comm hπ ((pEB_iff hπ e).1 he) ((pEB_iff hπ e').1 he')).eq)
  · rw [hF, card_cls03]
  · rw [hF, hE, card_cls03, card_cls0]
  · have hP : PbP e = true := by rw [← pEB_PbP hπ]; exact he
    obtain ⟨-, -, -, -, -, h1⟩ := (test2_spec (tst2 e.2)).2.2.1 hP
    have hac : allcP e = true := allN_of_forall fun k hk => by
      refine (cmP_iff hπ e.2 (sJ_rep hk) (J_le hπ (sJ_mem hk))).2 ?_
      obtain ⟨j, hj⟩ := elPF_surj hπ (J_le hπ (sJ_mem hk))
      rw [← hj]
      have := hc j
      unfold Commute SemiconjBy
      rw [← el_mulP hπ, ← el_mulP hπ, this]
    rcases h1 hac with h | h
    · left
      exact elPF_inj (by rw [el_oneP hπ]; exact (oneP_iff hπ e.2).1 h)
    · right
      exact elPF_inj (by rw [el_zP hπ]; exact (zP_iff hπ e.2).1 h)
  · rw [pFB_lam hπ]
    have h0 : lamP 0 (pOps.comm i j) = 0 := by
      rw [VOps.comm, lamP0_mulF hπ, lamP0_mulF hπ, lamP0_mulF hπ, lamP0_invF hπ, lamP0_invF hπ,
        Nat.xor_assoc (lamP 0 i ^^^ lamP 0 j), Nat.xor_self]
    rw [(lamP0_zero h0).2]
    rfl

theorem iterP (k : ℕ) (i : Fin 1024) : elP (pCc^[k] i) = cc ^ k * elP i * (cc ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', el_ccP hπ, ih]
    group

omit hπ in
theorem ccJ_iff {x : Equiv.Perm (Fin 1755)} : cc * x * cc⁻¹ ∈ titsJ ↔ x ∈ titsJ := by
  refine ⟨fun h => ?_, cc_norm⟩
  have h5 := cFacts.2.2.2.2.2
  have e : x = cc * (cc * (cc * (cc * (cc * x * cc⁻¹) * cc⁻¹) * cc⁻¹) * cc⁻¹) * cc⁻¹ := by
    have e5 : cc * cc * cc * cc * cc = 1 := by
      rw [← h5]
      simp only [pow_succ, pow_zero, one_mul]
    calc x = (cc * cc * cc * cc * cc) * x * (cc * cc * cc * cc * cc)⁻¹ := by rw [e5]; group
      _ = _ := by group
  rw [e]
  exact cc_norm (cc_norm (cc_norm (cc_norm h)))

omit hπ in
theorem ccpowJ_iff (k : ℕ) {x : Equiv.Perm (Fin 1755)} :
    cc ^ k * x * (cc ^ k)⁻¹ ∈ titsJ ↔ x ∈ titsJ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : cc ^ (k + 1) * x * (cc ^ (k + 1))⁻¹ = cc * (cc ^ k * x * (cc ^ k)⁻¹) * cc⁻¹ := by group
    rw [e, ccJ_iff, ih]

theorem lamP0_iter {k j : ℕ} (hk : k < 5) (hj : j < 5) (hkj : (k + j) % 5 = 0) (i : Fin 1024) :
    lamP 0 (pCc^[k] i) = lamP j i := by
  refine bits_eq6 (lamP_lt 0 _) (lamP_lt j i) fun m hm => ?_
  by_cases h5 : m = 5
  · subst h5
    rw [lamP_bit5' 0 (Fin.is_lt _), lamP_bit5' j i.2, iterP hπ, ccpowJ_iff]
  · have hm5 : m < 5 := by omega
    rw [lamP0_bit hπ (Fin.is_lt _) hm5, lamP_bit j i hm5,
      V.bool_not_of_iff (cmP_bc hπ i.2 hj hm5), iterP hπ, V.comm_conj_iff]
    have e : (cc ^ k)⁻¹ * el (bI m) * cc ^ k = bcg j m := by
      rw [bcg, ← V.cc_inv_pow hk hj hkj, inv_inv]
    rw [e, Commute.symm_iff (a := bcg j m)]

theorem words_mapP (i : Fin 1024) : ∀ (ks : List ℕ) (W : List (Fin 1024)),
    (ks.foldl (fun W k => W ++ W.map fun w => pOps.mul w (pCc^[k] i)) W).map
        (fun w : Fin 1024 => lamP 0 (w : ℕ)) =
      spanF (ks.map fun k => lamP 0 (pCc^[k] i : ℕ)) (W.map fun w : Fin 1024 => lamP 0 (w : ℕ))
  | [], _ => rfl
  | k :: ks, W => by
    have hf : ((fun w : Fin 1024 => lamP 0 (w : ℕ)) ∘ fun w => pOps.mul w (pCc^[k] i)) =
        ((fun a => a ^^^ lamP 0 (pCc^[k] i : ℕ)) ∘ fun w : Fin 1024 => lamP 0 (w : ℕ)) := by
      funext w
      simp only [Function.comp_apply]
      exact lamP0_mulF hπ w _
    rw [List.foldl_cons, words_mapP i ks, List.map_cons, spanF_cons, appL_eq, xorL_eq,
      List.map_append, List.map_map, List.map_map, hf]

theorem wordsOf_labelsP (i : Fin 1024) :
    (wordsOf pOps.mul pOps.one pCc i).map (fun w : Fin 1024 => lamP 0 (w : ℕ)) =
      spanF [lamP 0 i, lamP 4 i, lamP 3 i, lamP 2 i, lamP 1 i] [0] := by
  unfold wordsOf
  rw [words_mapP hπ i (List.range 5) [pOps.one]]
  have r5 : List.range 5 = [0, 1, 2, 3, 4] := rfl
  rw [r5]
  simp only [List.map_cons, List.map_nil]
  rw [lamP0_oneF hπ, lamP0_iter hπ (k := 0) (j := 0) (by norm_num) (by norm_num) (by norm_num),
    lamP0_iter hπ (k := 1) (j := 4) (by norm_num) (by norm_num) (by norm_num),
    lamP0_iter hπ (k := 2) (j := 3) (by norm_num) (by norm_num) (by norm_num),
    lamP0_iter hπ (k := 3) (j := 2) (by norm_num) (by norm_num) (by norm_num),
    lamP0_iter hπ (k := 4) (j := 1) (by norm_num) (by norm_num) (by norm_num)]

theorem pEB_of_lam {x : Fin 1024} (h : lamP 0 x = 0) : pEB x = true := by
  obtain ⟨hx, hl⟩ := lamP0_zero h
  rw [pEB_PbP hπ]
  cases hP : PbP x
  · have h3 := ((test2_spec (tst2 x.2)).2.2.2 hP).2.1 (by rw [hl]; rfl)
    exact absurd (clsP3 (Nat.eq_of_beq_eq_true h3.1)).1 (not_not.2 hx)
  · rfl

theorem lmP_ne {i : Fin 1024} (h : pFB i = false) : PbP i = false ∧ Nat.beq (lmP 0 i) 0 = false := by
  have spec := test2_spec (tst2 i.2)
  have hl : Nat.beq (lmP 0 i) 0 = false := by
    cases e : Nat.beq (lmP 0 i) 0
    · rfl
    · rw [(pFB_lam hπ i).2 e] at h
      exact absurd h (by decide)
  refine ⟨?_, hl⟩
  cases hP : PbP i
  · rfl
  · rw [(spec.2.2.1 hP).2.2.2.2.1] at hl
    exact absurd hl (by decide)

theorem vD2 : VCondsD2 pOps pEB pFB pRB pCc := by
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, fun x hx => ?_⟩
  · obtain ⟨hP, hl⟩ := lmP_ne hπ hi
    obtain ⟨-, -, hcov, -⟩ := (test2_spec (tst2 i.2)).2.2.2 hP |>.2.2 hl
    rw [List.all_eq_true]
    intro z _
    cases hz : pRB z
    · rfl
    · have hz5 : z.val < 512 := of_decide_eq_true hz
      rw [Bool.not_true, Bool.false_or, List.any_eq_true]
      have hzl : memN (lmP 0 z) LAM = true := (test2_spec (tst2 z.2)).1 (blt_lo hz5)
      rw [← lamP_lo hz5] at hzl
      have hv := (memN_iff _ _).1 ((allL_iff' _ _).1 hcov _ ((memN_iff _ _).1 hzl))
      rw [← wordsOf_labelsP hπ i, List.mem_map] at hv
      obtain ⟨w, hw, e⟩ := hv
      refine ⟨w, hw, pEB_of_lam hπ ?_⟩
      rw [lamP0_mulF hπ, lamP0_invF hπ, e, Nat.xor_self]
  · by_contra hne
    have hE : PbP x = false := by
      rw [← pEB_PbP hπ]
      cases e : pEB x
      · rfl
      · exact absurd e hne
    have hs := (((test2_spec (tst2 x.2)).2.2.2 hE).2.1 ((pFB_lam hπ x).1 hx)).2
    have : sqP x = true := (sqP_iff hπ x.2).2 (by rw [← el_mulP hπ, hx2, el_oneP hπ])
    rw [hs] at this
    exact Bool.false_ne_true this
  · have hP : PbP x = false := by rw [← pEB_PbP hπ]; exact hx
    obtain ⟨k, hk, hf⟩ : ∃ k < 4, (bIf(cmP x (TitsJ.S k), true, zcP x (TitsJ.S k))) = false := by
      by_contra hc
      push Not at hc
      have : PbP x = true := allN_of_forall fun k hk => by
        cases e : (bIf(cmP x (TitsJ.S k), true, zcP x (TitsJ.S k)))
        · exact absurd e (hc k hk)
        · rfl
      rw [hP] at this
      exact Bool.false_ne_true this
    have hz : ¬ Grp.Z0 titsZ ⁅elP x, sJ k⁆ := fun h => by
      rw [(pk_iff hπ x.2 hk).2 h] at hf
      exact Bool.noConfusion hf
    obtain ⟨r, hr⟩ := elPF_surj hπ (J_le hπ (sJ_mem hk))
    have hr5 : r.val < 512 := (elP_J_iff r.2).1 (by rw [hr]; exact sJ_mem hk)
    cases e : (List.finRange 1024).all (fun r => !pRB r ||
        (pOps.comm x r == pOps.one || pOps.comm x r == pOps.zI))
    · rfl
    · exfalso
      have h := List.all_eq_true.1 e r (List.mem_finRange r)
      have hR : pRB r = true := decide_eq_true hr5
      rw [hR, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
      refine hz ?_
      rw [← hr, ← el_commP hπ]
      rcases h with h | h
      · left
        rw [h, el_oneP hπ]
      · right
        rw [h, el_zP hπ]

theorem sq_tabP {i : ℕ} (hi : i < 1024) : ((pMulT[i]!)[i]! == pOneI) = sqP i := by
  refine Bool.eq_iff_iff.2 ?_
  rw [beq_iff_eq, sqP_iff hπ hi]
  obtain ⟨h1, h2⟩ := mulTP hπ hi hi
  constructor
  · intro e
    rw [← h2, e, (oneTP hπ).2]
  · intro e
    exact elP_inj h1 (oneTP hπ).1 (by rw [h2, e, (oneTP hπ).2])

theorem pFB_false {i : Fin 1024} (h : Nat.beq (lmP 0 i) 0 = false) : pFB i = false := by
  cases e : pFB i
  · rfl
  · rw [(pFB_lam hπ i).1 e] at h
    exact absurd h (by decide)

theorem pI0N_eq : pI0N = 129 := by
  have h : ∀ i ∈ List.range 1024,
      (!(pFBarr[i]!) && (pMulT[i]!)[i]! == pOneI) = Nat.beq (clsP i) 1 := by
    intro i hi
    have hi' := List.mem_range.1 hi
    have eF : pFBarr[i]! = pFB ⟨i, hi'⟩ := rfl
    rw [eF, sq_tabP hπ hi']
    have spec := test2_spec (tst2 hi')
    cases hP : PbP i
    · obtain ⟨-, s1, s2⟩ := spec.2.2.2 hP
      cases hl : Nat.beq (lmP 0 i) 0
      · rw [pFB_false hπ (i := ⟨i, hi'⟩) hl, (s2 hl).2.2.2]
        rfl
      · rw [(pFB_lam hπ ⟨i, hi'⟩).2 hl, Nat.eq_of_beq_eq_true (s1 hl).1]
        rfl
    · obtain ⟨-, h0, -, -, hl, -⟩ := spec.2.2.1 hP
      rw [(pFB_lam hπ ⟨i, hi'⟩).2 hl, Nat.eq_of_beq_eq_true h0]
      rfl
  unfold pI0N
  rw [V.find_congr h]
  decide +kernel

theorem pI0_eq : pI0 = ⟨129, by norm_num⟩ := by
  unfold pI0
  rw [pI0N_eq hπ]
  exact finPt_eq (by norm_num)

omit hπ in
theorem pWordAux_eq (par gl : Array ℕ) :
    ∀ fuel j, pWordAux par gl fuel j = wordT 1024 pI0N par gl fuel j
  | 0, _ => rfl
  | fuel + 1, j => by
    rw [pWordAux, wordT, pWordAux_eq par gl fuel]

omit hπ in
theorem pBfs_eq : pBfs = bfsT 1024 4 pI0N pCjT := rfl

theorem walk_elP : ∀ (L : List ℕ), (∀ k ∈ L, k < 3) → ∀ x < 1024,
    Bfs.walkT pCjT L x < 1024 ∧ elP (Bfs.walkT pCjT L x) = gw L * elP x * (gw L)⁻¹
  | [], _, x, hx => ⟨hx, by simp [Bfs.walkT, gw]⟩
  | k :: L, hL, x, hx => by
    obtain ⟨h1, h2⟩ := walk_elP L (fun k' h => hL k' (List.mem_cons_of_mem _ h)) x hx
    have hk := hL k List.mem_cons_self
    obtain ⟨c1, c2⟩ := cjTP hπ (k := k) (by omega) h1
    refine ⟨c1, ?_⟩
    change elP (pCjT[k]!)[Bfs.walkT pCjT L x]! = _
    have eg : genP k = hGen k := by simp only [genP, hk, ↓reduceIte]
    rw [c2, h2, eg]
    simp only [gw]
    group

theorem conjWord_walkP : ∀ (L : List ℕ), (∀ k ∈ L, k < 4) → ∀ x : Fin 1024,
    (conjWord pCj (L.map (finPt 4)) x : ℕ) = Bfs.walkT pCjT L x
  | [], _, x => rfl
  | k :: L, hL, x => by
    have hk := hL k List.mem_cons_self
    change (pCj (finPt 4 k) (conjWord pCj (L.map (finPt 4)) x) : ℕ) =
      (pCjT[k]!)[Bfs.walkT pCjT L x]!
    rw [cj_valP hπ, conjWord_walkP L (fun k' h => hL k' (List.mem_cons_of_mem _ h)) x,
      finPt_val hk]

omit hπ in
theorem cls129 : clsP 129 = 1 := by decide

theorem vE2 : VCondsE pOps pFB pCc pCj pI0 pWtab := by
  have h129 : (129 : ℕ) < 1024 := by norm_num
  have spec := test2_spec (tst2 h129)
  have hP : PbP 129 = false := by
    cases e : PbP 129
    · rfl
    · have := (spec.2.2.1 e).2.1
      rw [cls129] at this
      exact absurd this (by decide)
  have hl : Nat.beq (lmP 0 129) 0 = false := by
    cases e : Nat.beq (lmP 0 129) 0
    · rfl
    · have := ((spec.2.2.2 hP).2.1 e).1
      rw [cls129] at this
      exact absurd this (by decide)
  have hs : sqP 129 = true := by
    rw [← ((spec.2.2.2 hP).2.2 hl).2.2.2, cls129]
    rfl
  refine ⟨⟨?_, ?_⟩, fun j hjF hj2 => ?_, fun i hi => ?_⟩
  · rw [pI0_eq hπ]
    exact pFB_false hπ hl
  · rw [pI0_eq hπ]
    exact elPF_inj (by rw [el_mulP hπ, el_oneP hπ]; exact (sqP_iff hπ h129).1 hs)
  · obtain ⟨hPj, hlj⟩ := lmP_ne hπ hjF
    have hsj : sqP j = true := (sqP_iff hπ j.2).2 (by rw [← el_mulP hπ, hj2, el_oneP hπ])
    have hc : Nat.beq (clsP j) 1 = true := by
      rw [(((test2_spec (tst2 j.2)).2.2.2 hPj).2.2 hlj).2.2.2, hsj]
    obtain ⟨hj5, hcj⟩ := clsP1 (Nat.eq_of_beq_eq_true hc)
    have hinv := (memN_iff _ _).1 (V.cls_one (i := j) (by rw [hcj]; rfl))
    obtain ⟨w, hwW, hwc⟩ := V.wAll_spec INV WD V.wordsK j hinv
    have hw := V.WD_lt w hwW
    have hg := (V.wck_iff hj5 hw).1 hwc
    obtain ⟨wl, we⟩ := walk_elP hπ w hw 129 h129
    have hreach : Bfs.walkT pCjT w 129 = j :=
      elP_inj wl j.2 (by rw [we, elP_lo (i := 129) (by norm_num), elP_lo hj5, hg])
    have hadj : ∀ k < 4, ∀ x < 1024, (pCjT[k]!)[x]! < 1024 := fun k hk x hx => (cjTP hπ hk hx).1
    obtain ⟨b1, b2⟩ := bfs_word_sound (n := 1024) (m := 4) (fuel := 1200) h129 (by norm_num) hadj
      (fun k hk => by have := hw k hk; omega) hreach
    refine Fin.ext ?_
    unfold pWtab
    rw [pWordAux_eq, pBfs_eq, pI0N_eq hπ, pI0_eq hπ, conjWord_walkP hπ _ b1]
    exact b2
  · obtain ⟨hPi, hli⟩ := lmP_ne hπ hi
    have h4 := (((test2_spec (tst2 i.2)).2.2.2 hPi).2.2 hli).2.1
    cases e : pFB (pOps.mul (pCc i) (pOps.inv i))
    · rfl
    · exfalso
      have hl0 := (pFB_lam hπ _).1 e
      have hx := lamP0_mulF hπ (pCc i) (pOps.inv i)
      have h1 := lamP0_iter hπ (k := 1) (j := 4) (by norm_num) (by norm_num) (by norm_num) i
      rw [Function.iterate_one] at h1
      rw [lamP0_invF hπ, h1] at hx
      have hb5 : (lamP 0 (pOps.mul (pCc i) (pOps.inv i))).testBit 5 = false := by
        rw [hx, Nat.testBit_xor, lamP_bit5, lamP_bit5, Bool.xor_self]
      have hy : lamP 0 (pOps.mul (pCc i) (pOps.inv i)) = 0 := by
        by_cases hy5 : ((pOps.mul (pCc i) (pOps.inv i) : Fin 1024) : ℕ) < 512
        · rw [lamP_lo hy5]
          exact Nat.eq_of_beq_eq_true hl0
        · rw [lamP_bit5, blt_hi hy5] at hb5
          exact absurd hb5 (by decide)
      rw [hy] at hx
      have := V.xor_zero_eq hx.symm
      rw [this, Nat.beq_refl] at h4
      exact absurd h4 (by decide)

theorem vconds2 : VConds2 pOps pEB pFB pRB pCc pCj pI0 pWtab :=
  ⟨vA2, vB2 hπ, vC2 hπ, vD2 hπ, vE2 hπ⟩

theorem pbatch1 :
    pPel.size = 1024 ∧
    (allLt 1024 fun i => allLt 1024 fun j => decide ((pMulT[i]!)[j]! < 1024) &&
      titsJBase.all fun p => (pPel[(pMulT[i]!)[j]!]!)[p]! == (pPel[i]!)[(pPel[j]!)[p]!]!) = true ∧
    (allLt 1024 fun i => decide (pInvT[i]! < 1024) &&
      isInvA 1755 pPel[i]! (invCand 1755 pPel[i]!) &&
      eqA 1755 (invCand 1755 pPel[i]!) pPel[pInvT[i]!]!) = true ∧
    pOneI < 1024 ∧ eqA 1755 pPel[pOneI]! (idA 1755) = true ∧
    pZI < 1024 ∧ eqA 1755 pPel[pZI]! jZArr = true ∧
    (allLt 1024 fun i => allLt 1024 fun j => i == j ||
      titsJBase.any fun p => (pPel[i]!)[p]! != (pPel[j]!)[p]!) = true ∧
    (allLt 4 fun k => isInvA 1755 pGenArrs[k]! pGenInvArrs[k]!) = true ∧
    (allLt 4 fun k => allLt 1024 fun i => decide ((pCjT[k]!)[i]! < 1024) &&
      eqA 1755 (compA 1755 (compA 1755 pGenArrs[k]! pPel[i]!) pGenInvArrs[k]!)
        pPel[(pCjT[k]!)[i]!]!) = true ∧
    (allLt 1024 fun i => decide (pCcT[i]! < 1024) &&
      eqA 1755 (compA 1755 (compA 1755 jCArr pPel[i]!) jCInv) pPel[pCcT[i]!]!) = true ∧
    VConds2 pOps pEB pFB pRB pCc pCj pI0 pWtab := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := ptable_facts hπ
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, vconds2 hπ⟩

end CertificateChecks.KernelMisc.TitsJT.PV

end
