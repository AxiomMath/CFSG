module

public import Certificates.Kernel.Sporadic.Fi24Orb.Psi
public import Certificates.Kernel.Sporadic.Fi24Ext.Links
public import Certificates.Kernel.Sporadic.Fi24G2e.Data
public import Certificates.Kernel.VecCert.WordProgX
import Certificates.Kernel.Sporadic.Fi24Fix.Chain
import Certificates.Kernel.Sporadic.Fi24G2e.BV
import Certificates.Kernel.Sporadic.Fi24G2e.B0
import Certificates.Kernel.Sporadic.Fi24G2e.B1
import Certificates.Kernel.Sporadic.Fi24G2e.B2
import all CFSG.Sporadic.Bridge.Common
import Mathlib.Tactic.Group
public import Certificates.Kernel.Fi23M.Psi

public section

namespace CertificateChecks.KernelFi24G2e

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 CertificateChecks.KernelFi24Fix
  CertificateChecks.KernelFi24Orb CertificateChecks.KernelFi24Ext CertificateChecks.KernelSpor.Fi24Rels
  TauCeti TauCeti.Sporadic CFSG.Sporadic.Bridge CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS CFSG.KC.Fi24FixK
  CFSG.KS.Mat3 CFSG.KD.Fi24G2e

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24G2e.BX CFSG.KD.Fi24Ext.MX CFSG.KD.BrFi24.MT
  CFSG.KD.Fi24Fix.MX

theorem vld_all : ∀ k < 19, CFSG.KD.BrFi24.VLD (BX k) = true := CFSG.KD.Fi24G2e.BV.all

theorem cn_BX {k : ℕ} (hk : k < 19) : Cn (BX k) := hs.vld_q _ (vld_all k hk)

theorem eq_of_beq {X Y : ℕ} (h : Nat.beq X Y = true) : X = Y := Nat.eq_of_beq_eq_true h

theorem mt_RB {k : ℕ} (hk : k < 11) : Mt (CFSG.KD.BrFi24.RB (k + 1)) = (xs k).val :=
  ((xs_img k hk).trans (CertificateChecks.KernelSpor.Fi24Img.img_eq k hk)).symm

theorem cn_RB {k : ℕ} (hk : k < 11) : Cn (CFSG.KD.BrFi24.RB (k + 1)) :=
  canon_letM (l := (k, true)) hk

theorem mt_mul_one {X Y : ℕ} (hX : Cn X) (hY : Cn Y)
    (h : Nat.beq (CFSG.KD.BrFi24.MUL X Y) CFSG.KD.BrFi24.ONE = true) : Mt X * Mt Y = 1 := by
  rw [← (mul_mt hX hY).2, eq_of_beq h, mt_one]

theorem mt_mul_eq {X Y Z : ℕ} (hX : Cn X) (hY : Cn Y)
    (h : Nat.beq (CFSG.KD.BrFi24.MUL X Y) Z = true) : Mt X * Mt Y = Mt Z := by
  rw [← (mul_mt hX hY).2, eq_of_beq h]

theorem cn_Q : Cn CFSG.KD.Fi24Fix.Q :=
  canon_of_vld (andB_true3 (andB_true3 (andB_true3 CFSG.KD.Fi24Fix.valid).2).2).1

theorem tp_sq : Mt (LG 0) * Mt (LG 0) = 1 :=
  mt_mul_one (cn_BX (by norm_num)) (cn_BX (by norm_num)) CFSG.KD.Fi24G2e.B0.sq

@[expose] noncomputable def uT : GL (Fin 781) (ZMod 3) := ⟨Mt (LG 0), Mt (LG 0), tp_sq, tp_sq⟩

theorem uT_val : (uT : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (LG 0) := rfl

theorem uT_mul_uT : uT * uT = 1 := Units.ext tp_sq

theorem uT_inv : uT⁻¹ = uT := inv_eq_of_mul_eq_one_right uT_mul_uT

theorem lk_all : ∀ k < 11, Nat.beq (CFSG.KD.BrFi24.MUL (BX 0) (CFSG.KD.BrFi24.RB (k + 1)))
    (BX (k + 1)) = true := CFSG.KD.Fi24G2e.B2.L.all

theorem sk_all : ∀ k < 11, Nat.beq (CFSG.KD.BrFi24.MUL (BX (k + 1)) (BX (k + 1)))
    CFSG.KD.BrFi24.ONE = true := CFSG.KD.Fi24G2e.B2.S.all

theorem mt_LG_succ {k : ℕ} (hk : k < 11) : Mt (LG (k + 1)) = Mt (LG 0) * (xs k).val := by
  rw [← mt_RB hk]
  exact (mt_mul_eq (cn_BX (by norm_num)) (cn_RB hk) (lk_all k hk)).symm

theorem uT_xs_sq {k : ℕ} (hk : k < 11) : (uT * xs k) * (uT * xs k) = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, uT_val, ← mt_LG_succ hk, Units.val_one]
  exact mt_mul_one (cn_BX (by omega)) (cn_BX (by omega)) (sk_all k hk)

theorem uT_conj_xs {k : ℕ} (hk : k < 11) : uT * xs k * uT = (xs k)⁻¹ := by
  have h := uT_xs_sq hk
  calc uT * xs k * uT = ((uT * xs k) * (uT * xs k)) * (xs k)⁻¹ := by group
    _ = (xs k)⁻¹ := by rw [h, one_mul]

@[expose] noncomputable def cE : E →* E := (MulAut.conjNormal (g0 0)).toMonoidHom

theorem cE_val (e : E) : ((cE e : E) : Fi24AutomorphismGroup) = g0 0 * e * g0 0 := by
  change g0 0 * (e : Fi24AutomorphismGroup) * (g0 0)⁻¹ = _
  rw [g0_inv]

theorem uT_conj (e : E) : uT * σE e * uT = σE (cE e) := by
  have key : ((MulAut.conj uT).toMonoidHom.comp σ) =
      σE.comp (cE.comp fi24PrimeGroupMulEquivCommutator.toMonoidHom) := by
    apply PresentedGroup.ext
    intro i
    have hi : i.val < 11 := lt_of_lt_of_eq i.isLt gcount
    have hg : (PresentedGroup.of i : fi24PrimePresentation.Group) =
        presGen fi24PrimePresentation i.val := by
      rw [presGen, dif_pos i.isLt]
    have he : cE (fi24PrimeGroupMulEquivCommutator (presGen fi24PrimePresentation i.val)) =
        (fi24PrimeGroupMulEquivCommutator (presGen fi24PrimePresentation i.val))⁻¹ := by
      apply Subtype.ext
      rw [cE_val, Subgroup.coe_inv, iso_presGen hi, mul_inv_rev, g0_inv, g0_inv]
      simp only [← mul_assoc, g0_mul_self, one_mul]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hg, σ_gen hi, uT_inv, uT_conj_xs hi, he, map_inv, σE_iso, σ_gen hi]
  obtain ⟨u, rfl⟩ := fi24PrimeGroupMulEquivCommutator.surjective e
  have h := DFunLike.congr_fun key u
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [σE_iso, ← h, uT_inv]

theorem parity_cases (a b : Multiplicative (ZMod 2)) (ha : a ≠ 1) (hb : b ≠ 1) : a * b = 1 := by
  revert a b
  decide

theorem not_mem_mul_mem {q p : Fi24AutomorphismGroup} (hq : q ∉ E) (hp : p ∈ E) : q * p ∉ E := by
  intro h
  exact hq (by simpa using E.mul_mem h (E.inv_mem hp))

theorem mem_mul_not_mem {q p : Fi24AutomorphismGroup} (hq : q ∈ E) (hp : p ∉ E) : q * p ∉ E := by
  intro h
  exact hp (by simpa using E.mul_mem (E.inv_mem hq) h)

theorem mul_mem_of_not {q p : Fi24AutomorphismGroup} (hq : q ∉ E) (hp : p ∉ E) : q * p ∈ E := by
  rw [mem_E_iff] at hq hp ⊢
  rw [map_mul]
  exact parity_cases _ _ hq hp

theorem g0_mul_mem {q : Fi24AutomorphismGroup} (hq : q ∉ E) : g0 0 * q ∈ E :=
  (mem_E_or q).resolve_left hq

@[expose] noncomputable def σG (q : Fi24AutomorphismGroup) : GL (Fin 781) (ZMod 3) := by
  classical exact if h : q ∈ E then σE ⟨q, h⟩ else 1

theorem σG_mem {q : Fi24AutomorphismGroup} (h : q ∈ E) : σG q = σE ⟨q, h⟩ := by
  unfold σG
  rw [dif_pos h]

theorem σG_mul {q p : Fi24AutomorphismGroup} (hq : q ∈ E) (hp : p ∈ E) :
    σG (q * p) = σG q * σG p := by
  rw [σG_mem (E.mul_mem hq hp), σG_mem hq, σG_mem hp, ← map_mul]
  rfl

theorem conj_mem {q : Fi24AutomorphismGroup} (hq : q ∈ E) : g0 0 * q * g0 0 ∈ E := by
  have := cE_val ⟨q, hq⟩
  rw [← this]
  exact (cE ⟨q, hq⟩).2

theorem uT_conjG {q : Fi24AutomorphismGroup} (hq : q ∈ E) :
    uT * σG q * uT = σG (g0 0 * q * g0 0) := by
  rw [σG_mem hq, uT_conj, σG_mem (conj_mem hq)]
  exact congrArg σE (Subtype.ext (cE_val _))

@[expose] noncomputable def τf (q : Fi24AutomorphismGroup) : GL (Fin 781) (ZMod 3) := by
  classical exact if q ∈ E then σG q else uT * σG (g0 0 * q)

theorem τf_mem {q : Fi24AutomorphismGroup} (h : q ∈ E) : τf q = σG q := by
  unfold τf
  rw [if_pos h]

theorem τf_not {q : Fi24AutomorphismGroup} (h : q ∉ E) : τf q = uT * σG (g0 0 * q) := by
  unfold τf
  rw [if_neg h]

theorem τf_mul (q p : Fi24AutomorphismGroup) : τf (q * p) = τf q * τf p := by
  by_cases hq : q ∈ E <;> by_cases hp : p ∈ E
  · rw [τf_mem (E.mul_mem hq hp), τf_mem hq, τf_mem hp, σG_mul hq hp]
  · rw [τf_not (mem_mul_not_mem hq hp), τf_mem hq, τf_not hp]
    have e : g0 0 * (q * p) = (g0 0 * q * g0 0) * (g0 0 * p) := by
      rw [mul_assoc (g0 0 * q), g0_mul_self_mul, mul_assoc]
    rw [e, σG_mul (conj_mem hq) (g0_mul_mem hp), ← uT_conjG hq]
    calc uT * (uT * σG q * uT * σG (g0 0 * p)) = (uT * uT) * σG q * (uT * σG (g0 0 * p)) := by
          group
      _ = σG q * (uT * σG (g0 0 * p)) := by rw [uT_mul_uT, one_mul]
  · rw [τf_not (not_mem_mul_mem hq hp), τf_not hq, τf_mem hp, ← mul_assoc (g0 0) q p,
      σG_mul (g0_mul_mem hq) hp, mul_assoc]
  · rw [τf_mem (mul_mem_of_not hq hp), τf_not hq, τf_not hp]
    have e : q * p = g0 0 * (g0 0 * q) * g0 0 * (g0 0 * p) := by
      rw [g0_mul_self_mul, mul_assoc, g0_mul_self_mul]
    rw [e, σG_mul (conj_mem (g0_mul_mem hq)) (g0_mul_mem hp), ← uT_conjG (g0_mul_mem hq)]
    group

@[expose] noncomputable def τ : Fi24AutomorphismGroup →* GL (Fin 781) (ZMod 3) where
  toFun := τf
  map_one' := by
    rw [τf_mem E.one_mem, σG_mem E.one_mem]
    exact map_one σE
  map_mul' := τf_mul

theorem τ_apply (q : Fi24AutomorphismGroup) : τ q = τf q := rfl

theorem τ_E (e : E) : τ e = σE e := by
  rw [τ_apply, τf_mem e.2, σG_mem e.2]

theorem τ_not {q : Fi24AutomorphismGroup} (h : q ∉ E) :
    τ q = uT * σE ⟨g0 0 * q, g0_mul_mem h⟩ := by
  rw [τ_apply, τf_not h, σG_mem (g0_mul_mem h)]

theorem τ_g0_zero : τ (g0 0) = uT := by
  rw [τ_not a_not_mem_E]
  have : (⟨g0 0 * g0 0, g0_mul_mem a_not_mem_E⟩ : E) = 1 := Subtype.ext (g0_mul_self 0)
  rw [this, map_one, mul_one]

theorem τ_g0_succ {k : ℕ} (hk : k < 11) : τ (g0 (k + 1)) = uT * xs k := by
  have hn : g0 (k + 1) ∉ E := by
    rw [mem_E_iff, parity_g0 (by omega)]
    decide
  rw [τ_not hn]
  have : (⟨g0 0 * g0 (k + 1), g0_mul_mem hn⟩ : E) =
      fi24PrimeGroupMulEquivCommutator (presGen fi24PrimePresentation k) :=
    Subtype.ext (iso_presGen hk).symm
  rw [this, σE_iso, σ_gen hk]

theorem τ_g0 {g : ℕ} (hg : g < 12) : (τ (g0 g) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (LG g) := by
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · rw [τ_g0_zero, uT_val]
  · obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
    rw [τ_g0_succ (by omega), Units.val_mul, uT_val, mt_LG_succ (by omega)]

theorem cn_LG {g : ℕ} (hg : g < 12) : Cn (LG g) := cn_BX (by omega)

theorem wordMul_τ {Y : ℕ} (hY : Cn Y) : ∀ w : List ℕ, (∀ g ∈ w, g < 12) →
    Cn (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w Y) ∧
      Mt (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w Y) =
        (τ (w.map g0).prod : Matrix (Fin 781) (Fin 781) (ZMod 3)) * Mt Y
  | [], _ => ⟨hY, by simp [CFSG.KC.Fi24Fix.wordMul]⟩
  | g :: w, hw => by
    obtain ⟨h1, h2⟩ := wordMul_τ hY w (fun g' hg' => hw g' (List.mem_cons_of_mem g hg'))
    have e : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (g :: w) Y =
        CFSG.KD.BrFi24.MUL (LG g) (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w Y) := rfl
    obtain ⟨h3, h4⟩ := mul_mt (cn_LG (hw g List.mem_cons_self)) h1
    rw [e]
    refine ⟨h3, ?_⟩
    rw [h4, h2, List.map_cons, List.prod_cons, map_mul, Units.val_mul, τ_g0 (hw g List.mem_cons_self),
      Matrix.mul_assoc]

theorem uT_mem_stab : uT ∈ stab V0 := by
  have hTQ : Mt (LG 0) * Mt CFSG.KD.Fi24Fix.Q = Mt TQ :=
    mt_mul_eq (cn_BX (by norm_num)) cn_Q CFSG.KD.Fi24G2e.B0.tq
  have hkq : Mt CFSG.KD.Fi24Fix.Q * Mt TQ = Mt TQ :=
    mt_mul_eq cn_Q (cn_BX (by norm_num)) CFSG.KD.Fi24G2e.B0.kq
  have hle : act uT V0 ≤ V0 := by
    unfold act
    rw [uT_val, V0, ← range_mul, hTQ]
    exact range_le_of_mul_eq hkq
  rw [mem_stab]
  refine le_antisymm hle ?_
  have h2 : act uT (act uT V0) ≤ act uT V0 := Submodule.map_mono hle
  rwa [← act_mul, uT_mul_uT, act_one] at h2

theorem act_uT_V0 : act uT V0 = V0 := mem_stab.1 uT_mem_stab

theorem F_eq (q : Fi24AutomorphismGroup) : F q = act (τ q)⁻¹ V0 := by
  by_cases hq : q ∈ E
  · have h := F_mul 1 ⟨q, hq⟩
    rw [one_mul, F_one] at h
    rw [h, show τ q = σE ⟨q, hq⟩ from τ_E ⟨q, hq⟩]
  · have h1 : F (g0 0 * q) = F q := F_rel (by rw [mul_inv_cancel_right]; exact a_mem_H1)
    have h2 := F_mul 1 ⟨g0 0 * q, g0_mul_mem hq⟩
    rw [one_mul, F_one] at h2
    rw [← h1, h2, τ_not hq, mul_inv_rev, act_mul, uT_inv, act_uT_V0]

theorem F_τ (q p : Fi24AutomorphismGroup) : F (q * p) = act (τ p)⁻¹ (F q) := by
  rw [F_eq, F_eq, map_mul, mul_inv_rev, act_mul]

theorem ψ_walk_τ {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {r : ℕ} (hr : r < 306936) :
    ψ (walk CFSG.KD.Fi24Fix.TG w r) = act (τ (w.map g0).prod)⁻¹ (ψ r) := by
  rw [ψ_walk hw hr, F_τ]
  rfl

theorem ψ_TG {g : ℕ} (hg : g < 12) {r : ℕ} (hr : r < 306936) :
    ψ (CFSG.KD.Fi24Fix.TG g r) = act (τ (g0 g)) (ψ r) := by
  have h := ψ_walk_τ (w := [g]) (by simpa using hg) hr
  rw [walk_cons, walk_nil] at h
  rw [h, List.map_singleton, List.prod_singleton, ← map_inv, g0_inv]

@[expose] noncomputable def pl : List (ℕ × Bool) :=
  PL.map fun r => if r ≤ 11 then (r - 1, true) else (r - 12, false)

theorem pl_regs : pl.map regIdx = PL := by decide +kernel

theorem pl_lt : ∀ l ∈ pl, l.1 < 11 := by decide +kernel

theorem PL_split : PL = PC0 ++ PC1 ++ PC2 ++ PC3 ++ PC4 ++ PC5 := by decide +kernel

theorem wordMul_RB_append (u v : List ℕ) (Y : ℕ) :
    CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB (u ++ v) Y =
      CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB u
        (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB v Y) := by
  induction u with
  | nil => rfl
  | cons k u ih => exact congrArg (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB k)) ih

theorem PM_eq : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PL
    CFSG.KD.BrFi24.ONE = PM := by
  have e0 : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC5 CFSG.KD.BrFi24.ONE =
      BX 14 := eq_of_beq CFSG.KD.Fi24G2e.B1.p0
  have e1 : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC4 (BX 14) = BX 15 :=
    eq_of_beq CFSG.KD.Fi24G2e.B1.p1
  have e2 : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC3 (BX 15) = BX 16 :=
    eq_of_beq CFSG.KD.Fi24G2e.B1.p2
  have e3 : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC2 (BX 16) = BX 17 :=
    eq_of_beq CFSG.KD.Fi24G2e.B1.p3
  have e4 : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC1 (BX 17) = BX 18 :=
    eq_of_beq CFSG.KD.Fi24G2e.B1.p4
  have e5 : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC0 (BX 18) = PM :=
    eq_of_beq CFSG.KD.Fi24G2e.B1.p5
  rw [PL_split]
  simp only [List.append_assoc, wordMul_RB_append]
  rw [e0, e1, e2, e3, e4, e5]

@[expose] noncomputable def uP : GL (Fin 781) (ZMod 3) := wordProd xs pl

theorem uP_val : (uP : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt PM := by
  have hxR : ∀ g < 11, (xs g).val = mat3 781 609961 (CFSG.KD.BrFi24.RB (g + 1)) := fun g hg =>
    (mt_RB hg).symm
  have hw := (wordMul_mat cn_one pl pl_lt).2
  rw [pl_regs, PM_eq] at hw
  rw [uP, CertificateChecks.KernelWPX.val_wordProd hs hroot hinv hxR pl_lt,
    ← Matrix.mul_one (List.prod _), ← mt_one]
  exact hw.symm

theorem uP_mem : uP ∈ Γ := by
  unfold uP wordProd
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  rcases l with ⟨g, s⟩
  cases s
  · exact Γ.inv_mem (xs_mem g)
  · exact xs_mem g

theorem uT_eq (t : GL (Fin 781) (ZMod 3)) (ht : (t : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
    Mt CFSG.KD.Fi24Ext.T) : uT = uP * t * uP⁻¹ := by
  have h : uT * uP = uP * t := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, uT_val, uP_val, ht]
    exact (mt_mul_eq (cn_BX (by norm_num)) (cn_BX (by norm_num)) CFSG.KD.Fi24G2e.B0.lk).trans
      (mul_mt (cn_BX (by norm_num)) (cn_MX (k := 35) (by norm_num))).2
  rw [← h]
  group

theorem τ_mem_closure (t : GL (Fin 781) (ZMod 3)) (ht : (t : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
    Mt CFSG.KD.Fi24Ext.T) (q : Fi24AutomorphismGroup) :
    τ q ∈ Subgroup.closure ((Γ : Set (GL (Fin 781) (ZMod 3))) ∪ {t}) := by
  have hΓ : ∀ e : E, σE e ∈ Subgroup.closure ((Γ : Set (GL (Fin 781) (ZMod 3))) ∪ {t}) := by
    intro e
    obtain ⟨u, rfl⟩ := fi24PrimeGroupMulEquivCommutator.surjective e
    rw [σE_iso]
    exact Subgroup.subset_closure (Or.inl ⟨u, rfl⟩)
  have hP : uP ∈ Subgroup.closure ((Γ : Set (GL (Fin 781) (ZMod 3))) ∪ {t}) :=
    Subgroup.subset_closure (Or.inl uP_mem)
  have hT : uT ∈ Subgroup.closure ((Γ : Set (GL (Fin 781) (ZMod 3))) ∪ {t}) := by
    rw [uT_eq t ht]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hP (Subgroup.subset_closure (Or.inr rfl)))
      (Subgroup.inv_mem _ hP)
  by_cases hq : q ∈ E
  · rw [show τ q = σE ⟨q, hq⟩ from τ_E ⟨q, hq⟩]
    exact hΓ _
  · rw [τ_not hq]
    exact Subgroup.mul_mem _ hT (hΓ _)

end CertificateChecks.KernelFi24G2e

end
