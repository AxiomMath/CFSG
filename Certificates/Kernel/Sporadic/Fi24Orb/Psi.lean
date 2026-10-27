
module

public import Certificates.Kernel.Sporadic.Fi24Fix.Final
public import Certificates.Kernel.Sporadic.Fi24Orb.Joined
import Certificates.Kernel.Sporadic.Fi24Fix.Neg
import Certificates.Kernel.Sporadic.Fi24Fix.Chain
import Certificates.Kernel.Sporadic.Fi24Orb.Small
import all CFSG.Sporadic.Bridge.Common
import Mathlib.Tactic.Group
public import Certificates.Kernel.Fi23M.Psi
public import CFSG.Sporadic.Fi24.CertificateBase

public section

namespace CertificateChecks.KernelFi24Orb

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 CertificateChecks.KernelFi24Fix
  TauCeti TauCeti.Sporadic CFSG.Sporadic.Bridge CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS
  CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb CFSG.KC.Fi24OrbS CFSG.KS.Mat3

noncomputable def xs : ℕ → GL (Fin 781) (ZMod 3) := Classical.choose matFacts

theorem xs_img : ∀ k < 11, ((xs k : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
    CFSG.KD.Fi24Img.img k := (Classical.choose_spec matFacts).1

theorem xs_one : ∀ k, 11 ≤ k → xs k = 1 := (Classical.choose_spec matFacts).2.1

theorem xs_rel : ∀ v ∈ fi24PrimePresentation.relatorLetters, wordProd xs v = 1 :=
  (Classical.choose_spec matFacts).2.2.1

theorem xs_cl : ∀ g : GL (Fin 781) (ZMod 3), g.val = CFSG.Sporadic.Fi24.mA ∨
    g.val = CFSG.Sporadic.Fi24.mB → g ∈ Subgroup.closure (xs '' Set.Iio 11) :=
  (Classical.choose_spec matFacts).2.2.2.1

theorem xs_stab : ∀ k, k < 8 ∨ k = 9 → xs k ∈ stab V0 := (Classical.choose_spec matFacts).2.2.2.2.1

theorem xs_root : act (wordProd xs pv) (CFSG.Sporadic.Fi24.pt 0).sp = V0 :=
  (Classical.choose_spec matFacts).2.2.2.2.2.1

theorem xs_A : (((xs 7 * xs 10 : GL (Fin 781) (ZMod 3))) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
    CFSG.Sporadic.Fi24.mA := (Classical.choose_spec matFacts).2.2.2.2.2.2

noncomputable def σ : fi24PrimePresentation.Group →* GL (Fin 781) (ZMod 3) :=
  presHom fi24PrimePresentation xs xs_rel

noncomputable def σE : E →* GL (Fin 781) (ZMod 3) :=
  σ.comp fi24PrimeGroupMulEquivCommutator.symm.toMonoidHom

theorem σE_iso (u : fi24PrimePresentation.Group) : σE (fi24PrimeGroupMulEquivCommutator u) = σ u := by
  simp [σE]

theorem σ_gen {k : ℕ} (hk : k < 11) : σ (presGen fi24PrimePresentation k) = xs k :=
  presHom_presGen _ _ _ (by rw [gcount]; exact hk)

noncomputable abbrev Γ : Subgroup (GL (Fin 781) (ZMod 3)) := σ.range

theorem xs_mem (k : ℕ) : xs k ∈ Γ := by
  rcases Nat.lt_or_ge k 11 with hk | hk
  · exact ⟨_, σ_gen hk⟩
  · rw [xs_one k hk]
    exact Γ.one_mem

theorem cl_le : Subgroup.closure (xs '' Set.Iio 11) ≤ Γ := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact xs_mem k

theorem Γ_le' : Γ ≤ Subgroup.closure (xs '' Set.Iio 11) := by
  change σ.range ≤ _
  rw [MonoidHom.range_eq_map]
  have htop : (⊤ : Subgroup fi24PrimePresentation.Group) =
      Subgroup.closure (Set.range (PresentedGroup.of (rels := fi24PrimePresentation.relatorSet))) :=
    (PresentedGroup.closure_range_of _).symm
  rw [htop, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  have hi : i.val < 11 := lt_of_lt_of_eq i.isLt gcount
  have e : σ (PresentedGroup.of i) = xs i.val := by
    have := σ_gen hi
    rw [presGen, dif_pos i.isLt] at this
    exact this
  rw [e]
  exact Subgroup.subset_closure ⟨i.val, hi, rfl⟩

theorem seeds_mem (g : GL (Fin 781) (ZMod 3)) (hg : g.val = CFSG.Sporadic.Fi24.mA ∨
    g.val = CFSG.Sporadic.Fi24.mB) : g ∈ Γ := cl_le (xs_cl g hg)

theorem stab_H0 : ∀ (h : Fi24AutomorphismGroup), h ∈ H0 → ∀ hh : h ∈ E, σE ⟨h, hh⟩ ∈ stab V0 := by
  intro h hm
  induction hm using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    intro hh
    have hk : hgen j - 1 < 11 := by have := hgen_lt hj; omega
    have hg1 : 1 ≤ hgen j := by
      by_cases h8 : j = 8 <;> simp [hgen, h8]
    have e : (⟨g0 0 * g0 (hgen j), hh⟩ : E) =
        fi24PrimeGroupMulEquivCommutator (presGen fi24PrimePresentation (hgen j - 1)) := by
      apply Subtype.ext
      rw [iso_presGen hk, Nat.sub_add_cancel hg1]
    rw [e, σE_iso, σ_gen hk]
    apply xs_stab
    by_cases h8 : j = 8
    · subst h8
      right
      rfl
    · left
      have : hgen j = j + 1 := by simp [hgen, h8]
      have hj9 : j < 9 := hj
      omega
  | one =>
    intro hh
    have : (⟨1, hh⟩ : E) = 1 := rfl
    rw [this, map_one]
    exact (stab V0).one_mem
  | mul y z hy hz ihy ihz =>
    intro hh
    have : (⟨y * z, hh⟩ : E) = ⟨y, H0_le_E hy⟩ * ⟨z, H0_le_E hz⟩ := rfl
    rw [this, map_mul]
    exact (stab V0).mul_mem (ihy (H0_le_E hy)) (ihz (H0_le_E hz))
  | inv y hy ihy =>
    intro hh
    have : (⟨y⁻¹, hh⟩ : E) = (⟨y, H0_le_E hy⟩ : E)⁻¹ := rfl
    rw [this, map_inv]
    exact (stab V0).inv_mem (ihy (H0_le_E hy))

theorem stab_H1 : ∀ (h : Fi24AutomorphismGroup) (hh : h ∈ E), h ∈ H1 → σE ⟨h, hh⟩ ∈ stab V0 :=
  fun h hh hH => stab_H0 h (H1_inf_E hH hh) hh

noncomputable def F : Fi24AutomorphismGroup → Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
  subOf E (g0 0) mem_E_or σE V0

theorem F_rel {u v : Fi24AutomorphismGroup} (h : u * v⁻¹ ∈ H1) : F u = F v :=
  subOf_eq_of_rel a_mem_H1 stab_H1 h

theorem F_mul (q : Fi24AutomorphismGroup) (e : E) : F (q * e) = act (σE e)⁻¹ (F q) :=
  subOf_mul q e

theorem F_one : F 1 = V0 := by
  rw [F, subOf_eq_of_mem 1 E.one_mem]
  have : (⟨1, E.one_mem⟩ : E) = 1 := rfl
  rw [this, map_one, inv_one, act_one]

theorem F_mem (q : Fi24AutomorphismGroup) : ∃ g ∈ Γ, F q = act g V0 := by
  refine ⟨(σE ⟨ev E (g0 0) q, ev_mem mem_E_or q⟩)⁻¹, Γ.inv_mem ?_, rfl⟩
  obtain ⟨u, hu⟩ := fi24PrimeGroupMulEquivCommutator.surjective ⟨ev E (g0 0) q, ev_mem mem_E_or q⟩
  rw [← hu, σE_iso]
  exact ⟨u, rfl⟩

noncomputable def Rr : ℕ → Fi24AutomorphismGroup := Classical.choose rankFacts

theorem Rr_zero : Rr 0 = 1 := (Classical.choose_spec rankFacts).1

theorem Rr_T : ∀ g < 12, ∀ i < 306936, CFSG.KD.Fi24Fix.TG g i < 306936 ∧
    Rr i * g0 g * (Rr (CFSG.KD.Fi24Fix.TG g i))⁻¹ ∈ H1 := (Classical.choose_spec rankFacts).2.1

theorem Rr_cov : ∀ q, ∃ i < 306936, q * (Rr i)⁻¹ ∈ H1 := (Classical.choose_spec rankFacts).2.2

@[expose] noncomputable def ψ (r : ℕ) : Submodule (ZMod 3) (Fin 781 → ZMod 3) := F (Rr r)

theorem ψ_def (r : ℕ) : ψ r = F (Rr r) := rfl

theorem ψ_zero : ψ 0 = V0 := by
  rw [ψ, Rr_zero, F_one]

theorem walk_lt {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {r : ℕ} (hr : r < 306936) :
    walk CFSG.KD.Fi24Fix.TG w r < 306936 :=
  (walk_rel H1 Rr g0 CFSG.KD.Fi24Fix.TG Rr_T w hw r hr).1

theorem ψ_walk {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {r : ℕ} (hr : r < 306936) :
    ψ (walk CFSG.KD.Fi24Fix.TG w r) = F (Rr r * (w.map g0).prod) :=
  (F_rel (walk_rel H1 Rr g0 CFSG.KD.Fi24Fix.TG Rr_T w hw r hr).2).symm

theorem ψ_walk_E {w : List ℕ} (hw : ∀ g ∈ w, g < 12) (e : E)
    (he : (w.map g0).prod = (e : Fi24AutomorphismGroup)) {r : ℕ} (hr : r < 306936) :
    ψ (walk CFSG.KD.Fi24Fix.TG w r) = act (σE e)⁻¹ (ψ r) := by
  rw [ψ_walk hw hr, he, F_mul]
  rfl

theorem tk_eq (k r : ℕ) : tk CFSG.KD.Fi24Fix.TG k r = walk CFSG.KD.Fi24Fix.TG [0, k + 1] r := by
  rw [walk_cons, walk_cons, walk_nil]
  rfl

theorem tk_lt {k r : ℕ} (hk : k < 11) (hr : r < 306936) : tk CFSG.KD.Fi24Fix.TG k r < 306936 := by
  rw [tk_eq]
  exact walk_lt (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    omega) hr

theorem ψ_tk {k r : ℕ} (hk : k < 11) (hr : r < 306936) :
    ψ (tk CFSG.KD.Fi24Fix.TG k r) = act (xs k)⁻¹ (ψ r) := by
  rw [tk_eq]
  have hw : ∀ g ∈ [0, k + 1], g < 12 := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    omega
  rw [ψ_walk_E hw (fi24PrimeGroupMulEquivCommutator (presGen fi24PrimePresentation k)) ?_ hr,
    σE_iso, σ_gen hk]
  rw [iso_presGen hk]
  simp

noncomputable def uA : GL (Fin 781) (ZMod 3) := xs 7 * xs 10

theorem uA_val : (uA : Matrix (Fin 781) (Fin 781) (ZMod 3)) = CFSG.Sporadic.Fi24.mA := xs_A

theorem uA_mem : uA ∈ Γ := Γ.mul_mem (xs_mem 7) (xs_mem 10)

theorem σE_eA : σE eA = uA := by
  have e : eA = fi24PrimeGroupMulEquivCommutator
      (presGen fi24PrimePresentation 7 * presGen fi24PrimePresentation 10) := rfl
  rw [e, σE_iso, map_mul, σ_gen (by norm_num), σ_gen (by norm_num)]
  rfl

theorem AW_lt : ∀ g ∈ CFSG.KD.Fi24Fix.AW, g < 12 := by decide

theorem ψ_A {r : ℕ} (hr : r < 306936) : ψ (walk CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.AW r) =
    act uA (ψ r) := by
  rw [ψ_walk_E AW_lt eA⁻¹ (by rw [Subgroup.coe_inv, eA_inv_eq]) hr, map_inv, inv_inv, σE_eA]

@[expose] noncomputable def vL : List (ℕ × Bool) := (CFSG.KD.BrFi24.WC 11).map CFSG.KC.Ord.letC

@[expose] noncomputable def bL : List (ℕ × Bool) := (CFSG.KD.BrFi24.WC 12).map CFSG.KC.Ord.letC

theorem bL_eq : bL = vL ++ vL ++ vL ++ vL ++ vL ++ vL ++ vL := by decide +kernel

theorem vL_lt : ∀ l ∈ vL, l.1 < 11 := by decide +kernel

theorem bL_lt : ∀ l ∈ bL, l.1 < 11 := by
  intro l hl
  rw [bL_eq] at hl
  simp only [List.mem_append, or_self] at hl
  exact vL_lt l hl

@[expose] def invL : List (ℕ × Bool) → List ℕ
  | [] => []
  | l :: v => invL v ++ (if l.2 then [l.1 + 1, 0] else [0, l.1 + 1])

theorem invL_prod (v : List (ℕ × Bool)) :
    ((invL v).map g0).prod = (wordProd (fun k => g0 0 * g0 (k + 1)) v)⁻¹ := by
  induction v with
  | nil => simp [invL, wordProd]
  | cons l v ih =>
    rw [invL, List.map_append, List.prod_append, ih]
    obtain ⟨k, s⟩ := l
    cases s <;> simp [wordProd, g0_inv, mul_assoc]

@[expose] def redCons (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: u => if x = y then u else x :: y :: u

@[expose] def redL : List ℕ → List ℕ
  | [] => []
  | x :: w => redCons x (redL w)

theorem redCons_prod (x : ℕ) (v : List ℕ) :
    ((redCons x v).map g0).prod = g0 x * (v.map g0).prod := by
  cases v with
  | nil => simp [redCons]
  | cons y u =>
    by_cases h : x = y
    · subst h
      simp [redCons, g0_mul_self_mul]
    · simp [redCons, h]

theorem redL_prod (w : List ℕ) : ((redL w).map g0).prod = (w.map g0).prod := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [redL, redCons_prod, ih, List.map_cons, List.prod_cons]

theorem VW_eq : CFSG.KD.Fi24Orb.VW = redL (invL vL) := by decide +kernel

theorem VW_lt : ∀ g ∈ CFSG.KD.Fi24Orb.VW, g < 12 := by decide +kernel

theorem VW_prod : (CFSG.KD.Fi24Orb.VW.map g0).prod =
    (wordProd (fun k => g0 0 * g0 (k + 1)) vL)⁻¹ := by
  rw [VW_eq, redL_prod, invL_prod]

noncomputable def eB : E := fi24PrimeGroupMulEquivCommutator (wordProd (presGen fi24PrimePresentation) bL)

noncomputable def uB : GL (Fin 781) (ZMod 3) := σE eB

theorem uB_mem : uB ∈ Γ := by
  rw [uB, eB, σE_iso]
  exact ⟨_, rfl⟩

theorem uB_val : (uB : Matrix (Fin 781) (Fin 781) (ZMod 3)) = CFSG.Sporadic.Fi24.mB := by
  rw [uB, eB, σE_iso, σ, presHom_wordProd _ _ _ _ (fun l hl => by rw [gcount]; exact bL_lt l hl)]
  have hxR : ∀ g < 11, (xs g).val = mat3 781 609961 (CFSG.KD.BrFi24.RB (g + 1)) := fun g hg =>
    (xs_img g hg).trans (CertificateChecks.KernelSpor.Fi24Img.img_eq g hg)
  rw [CertificateChecks.KernelWPX.val_wordProd CertificateChecks.KernelSpor.Fi24Rels.hs
    CertificateChecks.KernelSpor.Fi24Rels.hroot CertificateChecks.KernelSpor.Fi24Rels.hinv hxR bL_lt]
  rw [CFSG.Sporadic.Fi24.mB, CertificateChecks.KernelSpor.Fi24Rels.mB_eq,
    Nat.eq_of_beq_eq_true CFSG.KD.Fi24Orb.b_state,
    (CertificateChecks.KernelSpor.Fi24Rels.goodS 12 (by norm_num)).2]
  unfold CertificateChecks.KernelWP.wordMat bL
  rw [List.map_map]
  rfl

theorem coe_eB : ((eB : E) : Fi24AutomorphismGroup) = wordProd (fun k => g0 0 * g0 (k + 1)) bL :=
  coe_iso_wordProd bL bL_lt

theorem VW7_prod : ((CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++
    CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW).map
      g0).prod = ((eB⁻¹ : E) : Fi24AutomorphismGroup) := by
  rw [Subgroup.coe_inv, coe_eB, bL_eq]
  simp only [List.map_append, List.prod_append, VW_prod]
  simp only [wordProd, List.map_append, List.prod_append, mul_inv_rev, mul_assoc]

theorem vt7_walk {r : ℕ} (hr : r < 306936) : vt7 CFSG.KD.Fi24Orb.VT r =
    walk CFSG.KD.Fi24Fix.TG (CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++
      CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW) r := by
  have hv : ∀ s < 306936, CFSG.KD.Fi24Orb.VT s < 306936 ∧
      CFSG.KD.Fi24Orb.VT s = walk CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Orb.VW s := fun s hs =>
    ⟨(CFSG.KD.Fi24Orb.vt_all s hs) ▸ walk_lt VW_lt hs, (CFSG.KD.Fi24Orb.vt_all s hs).symm⟩
  rw [vt7_eq]
  simp only [walk_append]
  obtain ⟨h1, e1⟩ := hv r hr
  obtain ⟨h2, e2⟩ := hv _ h1
  obtain ⟨h3, e3⟩ := hv _ h2
  obtain ⟨h4, e4⟩ := hv _ h3
  obtain ⟨h5, e5⟩ := hv _ h4
  obtain ⟨h6, e6⟩ := hv _ h5
  obtain ⟨-, e7⟩ := hv _ h6
  rw [e7, e6, e5, e4, e3, e2, e1]

theorem ψ_B {r : ℕ} (hr : r < 306936) : ψ (vt7 CFSG.KD.Fi24Orb.VT r) = act uB (ψ r) := by
  have hw : ∀ g ∈ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++
      CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW ++ CFSG.KD.Fi24Orb.VW,
      g < 12 := by
    intro g hg
    simp only [List.mem_append, or_self] at hg
    exact VW_lt g hg
  rw [vt7_walk hr, ψ_walk_E hw eB⁻¹ VW7_prod hr, map_inv, inv_inv]
  rfl

theorem vt7_lt {r : ℕ} (hr : r < 306936) : vt7 CFSG.KD.Fi24Orb.VT r < 306936 := by
  rw [vt7_walk hr]
  exact walk_lt (by
    intro g hg
    simp only [List.mem_append, or_self] at hg
    exact VW_lt g hg) hr

theorem PW_lt : ∀ g ∈ CFSG.KD.Fi24Fix.PW, g < 12 := by decide

theorem ψ_root : ψ (CFSG.KD.Fi24Orb.NM 0) = (CFSG.Sporadic.Fi24.pt 0).sp := by
  rw [Nat.eq_of_beq_eq_true CFSG.KD.Fi24Orb.n0, ψ_walk PW_lt (by norm_num), Rr_zero, one_mul,
    ← pE_eq]
  rw [F, subOf_eq_of_mem _ pE.2]
  change act (σE pE)⁻¹ V0 = _
  have hσp : σE pE = wordProd xs pv := by
    rw [σE_iso, σ, presHom_wordProd _ _ _ _ (fun l hl => by rw [gcount]; exact pv_lt l hl)]
  rw [hσp, ← xs_root, act_inv_act]

theorem idem_of {Q Y C : ℕ}
    (e1 : mat3 781 609961 (CFSG.KD.BrFi24.MUL Q Y) = mat3 781 609961 Q * mat3 781 609961 Y)
    (e2 : mat3 781 609961 (CFSG.KD.BrFi24.MUL Y C) = mat3 781 609961 Y * mat3 781 609961 C)
    (h1 : CFSG.KD.BrFi24.MUL Q Y = Y) (h2 : CFSG.KD.BrFi24.MUL Y C = Q) :
    mat3 781 609961 Q * mat3 781 609961 Q = mat3 781 609961 Q := by
  rw [h1] at e1
  rw [h2] at e2
  calc mat3 781 609961 Q * mat3 781 609961 Q =
      mat3 781 609961 Q * (mat3 781 609961 Y * mat3 781 609961 C) := by rw [← e2]
    _ = (mat3 781 609961 Q * mat3 781 609961 Y) * mat3 781 609961 C := (Matrix.mul_assoc _ _ _).symm
    _ = mat3 781 609961 Y * mat3 781 609961 C := by rw [← e1]
    _ = mat3 781 609961 Q := e2.symm

theorem keep_of_map {Q X : Matrix (Fin 781) (Fin 781) (ZMod 3)} (hQQ : Q * Q = Q)
    (h : (LinearMap.range Q.mulVecLin).map X.mulVecLin = LinearMap.range Q.mulVecLin) :
    Q * (X * Q) = X * Q := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hmem : (X * Q).mulVec w ∈ LinearMap.range Q.mulVecLin := by
    rw [← h]
    refine Submodule.mem_map.2 ⟨Q.mulVecLin w, LinearMap.mem_range_self Q.mulVecLin w, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  obtain ⟨u, hu⟩ := hmem
  rw [Matrix.mulVecLin_apply] at hu
  rw [← Matrix.mulVec_mulVec, ← hu, Matrix.mulVec_mulVec, hQQ, hu]

theorem x8_not_stab : xs 8 ∉ stab V0 := by
  intro h
  rw [mem_stab] at h
  have hQ : Canon3 609961 CFSG.KD.Fi24Fix.Q :=
    canon_of_vld (andB_true3 (andB_true3 (andB_true3 CFSG.KD.Fi24Fix.valid).2).2).1
  have hY : Canon3 609961 CFSG.KD.Fi24Fix.Y :=
    canon_of_vld (andB_true3 (andB_true3 CFSG.KD.Fi24Fix.valid).2).1
  have hC : Canon3 609961 CFSG.KD.Fi24Fix.C :=
    canon_of_vld (andB_true3 (andB_true3 (andB_true3 CFSG.KD.Fi24Fix.valid).2).2).2
  have hX : Canon3 609961 (CFSG.KD.BrFi24.RB 9) := canon_letM (l := (8, true)) (by norm_num)
  have hxv : (xs 8).val = mat3 781 609961 (CFSG.KD.BrFi24.RB 9) :=
    (xs_img 8 (by norm_num)).trans (CertificateChecks.KernelSpor.Fi24Img.img_eq 8 (by norm_num))
  have hQQ := idem_of (CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ hQ hY).2
    (CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ hY hC).2
    (Nat.eq_of_beq_eq_true CFSG.KD.Fi24Fix.span_le) (Nat.eq_of_beq_eq_true CFSG.KD.Fi24Fix.span_ge)
  unfold act at h
  rw [hxv] at h
  have hQXQ := keep_of_map hQQ h
  obtain ⟨hXQ, eXQ⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ hX hQ
  obtain ⟨hQXQc, eQXQ⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ hQ hXQ
  have heq : CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Fix.Q (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 9)
      CFSG.KD.Fi24Fix.Q) = CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 9) CFSG.KD.Fi24Fix.Q := by
    apply mat3_inj (d := 781) (by norm_num) hQXQc hXQ
    rw [eQXQ, eXQ]
    exact hQXQ
  have hk := CFSG.KD.Fi24Fix.Neg.keeps8
  unfold CFSG.KC.Fi24Fix.keepsOK at hk
  simp only [strictN_eq3] at hk
  rw [heq] at hk
  have : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 9) CFSG.KD.Fi24Fix.Q)
      (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 9) CFSG.KD.Fi24Fix.Q) = true := Nat.beq_refl _
  rw [this] at hk
  exact absurd hk (by decide)

end CertificateChecks.KernelFi24Orb

end
