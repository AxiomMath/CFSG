module

public import Certificates.Kernel.Fi23Y.KSCls
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23Facts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import Certificates.Data.CFSGNative.Schreier.SetOrbit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Y.KSF

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KC.Fi23Y CFSG.KD.Fi23K
  CFSG.KD.Fi23S CFSG.KD.Fi23R CFSG.KS.Raw.Orb CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum
  CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelFi23R
  CertificateChecks.KernelFi23M CertificateChecks.KernelFi23S CertificateChecks.KernelFi23Y.KSY
  CertificateChecks.KernelFi23Y.KSC
open CFSG.ComponentClassification.RankTwoSporadic (nE gammaE centDer monoW_map_iff)
open CFSG.ComponentClassification.RankTwoSporadic.Cert (MonoW)
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus (fixP fixP_conj)
open CFSG.ComponentClassification.RankTwoSporadic.Fi23 (fi23Fix Fi23CensusFactsOn)
open scoped commutatorElement

local notation "gLY" => CFSG.KD.Fi23Y.GL
local notation "CDY" => CFSG.KD.Fi23Y.CD
local notation "TRY" => CFSG.KD.Fi23Y.TR

private theorem eqB6_spec {f g : ℕ → ℕ} (h : eqB6 f g = true) : ∀ b < 6, f b = g b := by
  intro b hb
  unfold eqB6 at h
  exact Nat.eq_of_beq_eq_true (allN_iff.1 h b hb)

private theorem movB6_spec {f : ℕ → ℕ} (h : movB6 f = true) : ¬ ∀ b < 6, f b = b := by
  intro hall
  have e : eqB6 f (fun b => b) = true := by
    unfold eqB6
    exact allN_iff.2 fun b hb => by rw [Nat.beq_eq]; exact hall b hb
  unfold movB6 at h
  rw [e] at h
  exact absurd h (by decide)

private theorem root_spec {wt : ℕ → ℕ} {i : ℕ} (h : rootY gLY CDY LS wt i = true) :
    wt (4704 + i) < 262144 ∧ 1 < CDY (wt (4704 + i)) ∧ clsY CDY (wt (4704 + i)) = i ∧
      (∀ b < 6, gLY (wt (4704 + i)) (gLY (wt (4704 + i)) b) = b) ∧
      (¬ ∀ b < 6, gLY (wt (4704 + i)) b = b) ∧
      ∀ s < 42, ∀ b < 6, gLY (wt (4704 + i)) (LS s b) = LS s (gLY (wt (4704 + i)) b) := by
  unfold rootY at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3, eqB6_spec h4,
    movB6_spec h5, fun s hs => eqB6_spec (allN_iff.1 h6 s hs)⟩

private theorem rep_spec {wt : ℕ → ℕ} {r : ℕ} (h : repY CDY wt r = true) :
    wt (4608 + r) < 262144 ∧ 1 < CDY (wt (4608 + r)) := by
  unfold repY at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.blt_eq.mp h.2⟩

private theorem cen_spec {cj wt : ℕ → ℕ} {l : ℕ} (h : cenY gLY CDY cj wt l = true)
    (hc : 2 ≤ CDY l) : cj l &&& 127 < 96 ∧ cj l >>> 7 < 262144 ∧
      ∀ b < 6, gLY (cj l >>> 7) (gLY l b) =
        gLY (wt (4608 + (cj l &&& 127))) (gLY (cj l >>> 7) b) := by
  unfold cenY at h
  rw [bIf_eq, if_neg (fun hb => (Nat.not_lt.2 hc) (Nat.blt_eq.mp hb))] at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.blt_eq.mp h.2.1, eqB6_spec h.2.2⟩

private theorem ent_cases {wt : ℕ → ℕ} {i r : ℕ} (h : entY gLY TRY CDY wt i r = true) :
    wt (4608 + r) = wt (4704 + i) ∨
      witK gLY TRY wt (wt (4704 + i)) (wt (4608 + r)) (16 * (96 * i + r)) = true ∨
      (wt (16 * (96 * i + r) + 1) < i ∧ clsY CDY (wt (4608 + r)) = wt (16 * (96 * i + r) + 1)) ∨
      (wt (16 * (96 * i + r) + 1) < i ∧ wt (16 * (96 * i + r) + 2) < 262144 ∧
        1 < CDY (wt (16 * (96 * i + r) + 2)) ∧
        clsY CDY (wt (16 * (96 * i + r) + 2)) = wt (16 * (96 * i + r) + 1) ∧
        ∀ b < 6, gLY (wt (16 * (96 * i + r) + 2)) b =
          gLY (wt (4704 + i)) (gLY (wt (4608 + r)) b)) := by
  unfold entY at h
  simp only [strictB_eq, bAnd_eq] at h
  simp only [bIf_eq] at h
  split_ifs at h with h0 h1 h2
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · exact Or.inr (Or.inl h)
  · rw [Bool.and_eq_true] at h
    exact Or.inr (Or.inr (Or.inl ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩))
  · simp only [Bool.and_eq_true] at h
    obtain ⟨-, e1, e2, e3, e4, e5⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, Nat.blt_eq.mp e3,
      Nat.eq_of_beq_eq_true e4, eqB6_spec e5⟩))

private theorem witK_spec {wt : ℕ → ℕ} {lx lb base : ℕ} (h : witK gLY TRY wt lx lb base = true) :
    (∀ a < wt (base + 2), facOK gLY TRY wt lx lb base a = true) ∧
      (∀ b < 6, itN (wY gLY TRY wt lx lb base (wt (base + 2))) (4 * wt (base + 1)) b = b) ∧
      ¬ ∀ b < 6, itN (wY gLY TRY wt lx lb base (wt (base + 2))) (2 * wt (base + 1)) b = b := by
  unfold witK at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  exact ⟨allN_iff.1 h.1, eqB6_spec h.2.1, movB6_spec h.2.2⟩

private theorem facOK_spec {wt : ℕ → ℕ} {lx lb base a : ℕ}
    (h : facOK gLY TRY wt lx lb base a = true) :
    wt (base + (4 + 2 * a)) >>> 15 < 31671 ∧ wt (base + (4 + 2 * a)) &&& 32767 < 31671 ∧
      (∀ b < 6, selE gLY lx lb (wt (base + (3 + 2 * a)) / 3)
          (TRY (wt (base + (4 + 2 * a)) >>> 15) b) =
        TRY (wt (base + (4 + 2 * a)) >>> 15) (selE gLY lx lb (wt (base + (3 + 2 * a)) / 3) b)) ∧
      ∀ b < 6, selE gLY lx lb (wt (base + (3 + 2 * a)) / 3)
          (TRY (wt (base + (4 + 2 * a)) &&& 32767) b) =
        TRY (wt (base + (4 + 2 * a)) &&& 32767) (selE gLY lx lb (wt (base + (3 + 2 * a)) / 3) b) := by
  unfold facOK at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨-, h1, h2, h3, h4⟩ := h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, eqB6_spec h3, eqB6_spec h4⟩

private theorem wY_succ {wt : ℕ → ℕ} {lx lb base : ℕ} (a y : ℕ) :
    wY gLY TRY wt lx lb base (a + 1) y = facY gLY TRY lx lb (wt (base + (3 + 2 * a)) % 3)
      (wt (base + (4 + 2 * a)) >>> 15) (wt (base + (4 + 2 * a)) &&& 32767)
      (wY gLY TRY wt lx lb base a y) := by
  have e : wY gLY TRY wt lx lb base (a + 1) y =
      CFSG.KC.Enum.strictN (wY gLY TRY wt lx lb base a y) (fun z =>
        CFSG.KC.Enum.strictN (wt (base + (3 + 2 * a))) fun s =>
          CFSG.KC.Enum.strictN (wt (base + (4 + 2 * a))) fun kk =>
            facY gLY TRY lx lb (s % 3) (kk >>> 15) (kk &&& 32767) z) := rfl
  rw [e]
  simp only [strictN_eq]

private theorem eq_base {p q : Pt}
    (hp : p ∈ Xc) (hq : q ∈ Xc) (h : ∀ b < 6, actN p b = actN q b) : p = q :=
  base_eq hp hq fun i hi => by
    rw [← actN_eq_val p (i := i) (by omega), ← actN_eq_val q (i := i) (by omega)]
    exact h i hi

private theorem TR_eq {k y : ℕ}
    (hk : k < 31671) (hy : y < 31671) : TRY k y = actN (cT k) y := by
  rw [actN_eq_val _ hy]
  exact (cT_acts hk y hy).symm

private theorem LS_eq {s y : ℕ} (hs : s < 42) (hy : y < 31671) :
    LS s y = actN (sig 31671 SL s) y :=
  (actN_sig syl_hyp hs hy).symm

private theorem itN_eq {f : ℕ → ℕ} {p : Pt} (hf : ∀ y < 31671, f y = actN p y) :
    ∀ n, ∀ x < 31671, itN f n x = actN (p ^ n) x
  | 0, x, _ => by
    show x = actN (p ^ 0) x
    rw [pow_zero, actN_one]
  | n + 1, x, hx => by
    show strictN (itN f n x) f = _
    rw [strictN_eq, itN_eq hf n x hx, hf _ (actN_lt _ hx), pow_succ', actN_mul]

private theorem map_conj_mem {H : Subgroup Pt} {g : Pt} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hy) (Subgroup.inv_mem _ hg)
  · intro hx
    exact ⟨g⁻¹ * x * g,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hx) hg, by group⟩

private theorem sq_one_of_comm {M : Type*} [Group M] {a b : M} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h : a * b = b * a) : (a * b) ^ 2 = 1 := by
  rw [pow_two] at ha hb ⊢
  calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b) * b := by rw [← h]
    _ = a * a * (b * b) := by simp only [mul_assoc]
    _ = 1 := by rw [ha, hb, one_mul]

private theorem root_facts
    {wt : ℕ → ℕ} {i : ℕ} (h : rootY gLY CDY LS wt i = true) :
    lvP (wt (4704 + i)) ∈ Xc ∧ lvP (wt (4704 + i)) ^ 2 = 1 ∧ lvP (wt (4704 + i)) ≠ 1 ∧
      fixP (lvP (wt (4704 + i))) = fi23Fix[i]! ∧
      TY ≤ Subgroup.centralizer {lvP (wt (4704 + i))} ∧ wt (4704 + i) < 262144 := by
  obtain ⟨hz, hc, hcl, h2, h1, hs⟩ := root_spec h
  generalize wt (4704 + i) = z at hz hc hcl h2 h1 hs ⊢
  have hm := lvP_mem hz
  have hsq : lvP z ^ 2 = 1 := by
    refine one_of_fix (Subgroup.pow_mem _ hm 2) fun b hb => ?_
    have hb' : b < 31671 := by omega
    rw [pow_two, actN_mul, ← GL_eq hz hb', ← GL_eq hz (GL_lt hz hb')]
    exact h2 b hb
  refine ⟨hm, hsq, fun e => h1 fun b hb => ?_, ?_, ?_, hz⟩
  · have hb' : b < 31671 := by omega
    rw [GL_eq hz hb', e, actN_one]
  · rw [fixP_lvP hz hc hsq, hcl]
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    change sig 31671 SL s.val ∈ Subgroup.centralizer {lvP z}
    have hsX : sig 31671 SL s.val ∈ Xc := T23_le (sig_T23 s.isLt)
    refine Subgroup.mem_centralizer_singleton_iff.2
      (eq_base (Subgroup.mul_mem _ hsX hm) (Subgroup.mul_mem _ hm hsX) fun b hb => ?_)
    have hb' : b < 31671 := by omega
    have hL : LS s.val b < 31671 := by rw [LS_eq s.isLt hb']; exact actN_lt _ hb'
    rw [actN_mul, actN_mul, ← GL_eq hz hb', ← LS_eq s.isLt hb', ← LS_eq s.isLt (GL_lt hz hb'),
      ← GL_eq hz hL]
    exact (hs s.val s.isLt b hb).symm

private theorem inv_leaf {b : Pt}
    (hb : b ∈ TY) (h2 : b ^ 2 = 1) (h1 : b ≠ 1) : ∃ l < 262144, b = lvP l ∧ 2 ≤ CDY l := by
  obtain ⟨l, hl, rfl⟩ := exists_leaf hb
  refine ⟨l, hl, rfl, ?_⟩
  have hk := leaf_hi_lt hl
  have hj := leaf_lo_lt l
  rw [CD_eq]
  rcases lf13_cases (lf13_all hk hj) with ⟨-, x, hx, hne⟩ | ⟨-, hfix⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  · exfalso
    apply hne
    have hx' : x < 31671 := by omega
    rw [gK_eq hk hj (gK_lt hk hj hx'), gK_eq hk hj hx', ← actN_mul, ← lvP_eq, ← pow_two, h2,
      actN_one]
  · exfalso
    apply h1
    refine one_of_fix (lvP_mem hl) fun x hx => ?_
    have hx' : x < 31671 := by omega
    rw [lvP_eq, ← gK_eq hk hj hx']
    exact hfix x hx
  · exact hc
  · exact hc

private theorem conj_facts {M : Type*} [Group M] {x b t br : M} (hx2 : x ^ 2 = 1)
    (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) (hbx : b ≠ x) (hxb : x * b = b * x) (hxt : x * t = t * x)
    (htb : t * b = br * t) :
    br ^ 2 = 1 ∧ br ≠ 1 ∧ x * br ≠ 1 ∧ x * br = br * x ∧ t * (x * b) = x * br * t := by
  have hbr : br = t * b * t⁻¹ := by rw [htb, mul_inv_cancel_right]
  subst hbr
  have key : ∀ g : M, t * b * t⁻¹ = g → b = t⁻¹ * g * t := fun g e => by rw [← e]; group
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hx2])
  have hxti : x * t⁻¹ = t⁻¹ * x := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hxt, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨?_, fun e => hb1 ?_, fun e => hbx ?_, ?_, ?_⟩
  · rw [conj_pow, hb2, mul_one, mul_inv_cancel]
  · rw [key 1 e]
    group
  · have h' : t * b * t⁻¹ = x := by
      rw [← hxi]
      exact eq_inv_of_mul_eq_one_right e
    rw [key x h', mul_assoc, hxt, ← mul_assoc, inv_mul_cancel, one_mul]
  · calc x * (t * b * t⁻¹) = x * t * b * t⁻¹ := by group
      _ = t * x * b * t⁻¹ := by rw [hxt]
      _ = t * b * x * t⁻¹ := by rw [mul_assoc t x b, hxb, ← mul_assoc]
      _ = t * b * (x * t⁻¹) := by group
      _ = t * b * (t⁻¹ * x) := by rw [hxti]
      _ = t * b * t⁻¹ * x := by group
  · calc t * (x * b) = t * x * b := (mul_assoc _ _ _).symm
      _ = x * t * b := by rw [hxt]
      _ = x * (t * b * t⁻¹) * t := by group

private noncomputable def selP (lx lb s : ℕ) : Pt :=
  if Nat.beq s (nat_lit 0) = true then lvP lx
  else if Nat.beq s (nat_lit 1) = true then lvP lb else lvP lx * lvP lb

private noncomputable def facP (lx lb vs k1 k2 : ℕ) : Pt :=
  selP lx lb vs * cT k1 * cT k2 * cT k1 * cT k2 * selP lx lb vs * cT k2 * cT k1 * cT k2 * cT k1

private noncomputable def wP (wt : ℕ → ℕ) (lx lb base : ℕ) : ℕ → Pt
  | 0 => 1
  | a + 1 => facP lx lb (wt (base + (3 + 2 * a)) % 3) (wt (base + (4 + 2 * a)) >>> 15)
      (wt (base + (4 + 2 * a)) &&& 32767) * wP wt lx lb base a

private theorem selE_eq {lx lb : ℕ} (hlx : lx < 262144) (hlb : lb < 262144) (s : ℕ) {y : ℕ}
    (hy : y < 31671) : selE gLY lx lb s y = actN (selP lx lb s) y := by
  unfold selE selP
  rw [nIf_eq, nIf_eq, strictN_eq]
  split_ifs
  · exact GL_eq hlx hy
  · exact GL_eq hlb hy
  · rw [actN_mul, ← GL_eq hlb hy, ← GL_eq hlx (GL_lt hlb hy)]

private theorem selP_props
    {lx lb : ℕ} (hlx : lx < 262144) (hlb : lb < 262144) (hx2 : lvP lx ^ 2 = 1)
    (hb2 : lvP lb ^ 2 = 1) (hx1 : lvP lx ≠ 1) (hb1 : lvP lb ≠ 1) (hxb : lvP lx * lvP lb ≠ 1)
    (hc : lvP lx * lvP lb = lvP lb * lvP lx) (s : ℕ) :
    selP lx lb s ∈ Subgroup.closure ({lvP lx, lvP lb} : Set Pt) ∧ selP lx lb s ∈ Xc ∧
      selP lx lb s ≠ 1 ∧ selP lx lb s * selP lx lb s = 1 := by
  have hxE : lvP lx ∈ Subgroup.closure ({lvP lx, lvP lb} : Set Pt) :=
    Subgroup.subset_closure (by simp)
  have hbE : lvP lb ∈ Subgroup.closure ({lvP lx, lvP lb} : Set Pt) :=
    Subgroup.subset_closure (by simp)
  have hx2' : lvP lx * lvP lx = 1 := by rw [← pow_two, hx2]
  have hb2' : lvP lb * lvP lb = 1 := by rw [← pow_two, hb2]
  unfold selP
  split_ifs
  · exact ⟨hxE, lvP_mem hlx, hx1, hx2'⟩
  · exact ⟨hbE, lvP_mem hlb, hb1, hb2'⟩
  · refine ⟨Subgroup.mul_mem _ hxE hbE, Subgroup.mul_mem _ (lvP_mem hlx) (lvP_mem hlb), hxb, ?_⟩
    rw [← pow_two]
    exact sq_one_of_comm hx2 hb2 hc

private theorem facP_acts
    {lx lb vs k1 k2 : ℕ} (hlx : lx < 262144) (hlb : lb < 262144) (hk1 : k1 < 31671)
    (hk2 : k2 < 31671) : ActsAs (facP lx lb vs k1 k2) (facY gLY TRY lx lb vs k1 k2) := by
  have hV : ActsAs (selP lx lb vs) (selE gLY lx lb vs) := fun y hy => by
    rw [← actN_eq_val _ hy]
    exact (selE_eq hlx hlb vs hy).symm
  have h1 : ActsAs (cT k1) (TRY k1) := actsAs_congr (cT_acts hk1) fun _ _ => rfl
  have h2 : ActsAs (cT k2) (TRY k2) := actsAs_congr (cT_acts hk2) fun _ _ => rfl
  refine actsAs_congr
    (((((((((hV.mul h1).mul h2).mul h1).mul h2).mul hV).mul h2).mul h1).mul h2).mul h1)
    fun y _ => ?_
  unfold facY
  simp only [strictN_eq]

private theorem wP_acts
    {wt : ℕ → ℕ} {lx lb base n : ℕ} (hlx : lx < 262144) (hlb : lb < 262144)
    (hk : ∀ a < n, wt (base + (4 + 2 * a)) >>> 15 < 31671 ∧
      wt (base + (4 + 2 * a)) &&& 32767 < 31671) :
    ∀ m ≤ n, ActsAs (wP wt lx lb base m) (wY gLY TRY wt lx lb base m)
  | 0, _ => fun _ _ => rfl
  | m + 1, hm => by
    have ih := wP_acts hlx hlb hk m (by omega)
    obtain ⟨hk1, hk2⟩ := hk m (by omega)
    exact actsAs_congr ((facP_acts (vs := wt (base + (3 + 2 * m)) % 3) hlx hlb hk1 hk2).mul ih)
      fun y _ => (wY_succ m y).symm

private theorem selP_Xc
    {lx lb : ℕ} (hlx : lx < 262144) (hlb : lb < 262144) (s : ℕ) : selP lx lb s ∈ Xc := by
  unfold selP
  split_ifs
  · exact lvP_mem hlx
  · exact lvP_mem hlb
  · exact Subgroup.mul_mem _ (lvP_mem hlx) (lvP_mem hlb)

private theorem wP_Xc
    {wt : ℕ → ℕ} {lx lb base : ℕ} (hlx : lx < 262144) (hlb : lb < 262144) :
    ∀ m, wP wt lx lb base m ∈ Xc
  | 0 => Subgroup.one_mem _
  | m + 1 => by
    have hv := selP_Xc hlx hlb (wt (base + (3 + 2 * m)) % 3)
    have h1 := cT_mem (wt (base + (4 + 2 * m)) >>> 15)
    have h2 := cT_mem (wt (base + (4 + 2 * m)) &&& 32767)
    refine Subgroup.mul_mem _ ?_ (wP_Xc hlx hlb m)
    unfold facP
    repeat' first | exact hv | exact h1 | exact h2 | refine Subgroup.mul_mem _ ?_ ?_

private theorem facP_mem
    {lx lb : ℕ} (hlx : lx < 262144) (hlb : lb < 262144) (hx2 : lvP lx ^ 2 = 1)
    (hb2 : lvP lb ^ 2 = 1) (hx1 : lvP lx ≠ 1) (hb1 : lvP lb ≠ 1) (hxb : lvP lx * lvP lb ≠ 1)
    (hc : lvP lx * lvP lb = lvP lb * lvP lx) {vs es k1 k2 : ℕ} (hk1 : k1 < 31671)
    (hk2 : k2 < 31671)
    (h1 : ∀ b < 6, selE gLY lx lb es (TRY k1 b) = TRY k1 (selE gLY lx lb es b))
    (h2 : ∀ b < 6, selE gLY lx lb es (TRY k2 b) = TRY k2 (selE gLY lx lb es b)) :
    facP lx lb vs k1 k2 ∈ nE Xc (Subgroup.closure ({lvP lx, lvP lb} : Set Pt)) := by
  obtain ⟨heE, heX, he1, -⟩ := selP_props hlx hlb hx2 hb2 hx1 hb1 hxb hc es
  obtain ⟨hvE, -, -, hv2⟩ := selP_props hlx hlb hx2 hb2 hx1 hb1 hxb hc vs
  have comm : ∀ k < 31671,
      (∀ b < 6, selE gLY lx lb es (TRY k b) = TRY k (selE gLY lx lb es b)) →
      cT k ∈ Xc ⊓ Subgroup.centralizer ({selP lx lb es} : Set Pt) := fun k hk hb => by
    refine Subgroup.mem_inf.2 ⟨cT_mem k, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    refine eq_base (Subgroup.mul_mem _ (cT_mem k) heX) (Subgroup.mul_mem _ heX (cT_mem k))
      fun b hb' => ?_
    have hb31 : b < 31671 := by omega
    have hcb : actN (cT k) b < 31671 := actN_lt _ hb31
    have hsb : actN (selP lx lb es) b < 31671 := actN_lt _ hb31
    have := hb b hb'
    rw [TR_eq hk hb31, selE_eq hlx hlb es hb31, selE_eq hlx hlb es hcb, TR_eq hk hsb] at this
    rw [actN_mul, actN_mul]
    exact this.symm
  have hle : centDer Xc (selP lx lb es) ≤
      gammaE Xc (Subgroup.closure ({lvP lx, lvP lb} : Set Pt)) :=
    le_iSup₂_of_le (f := fun t (_ : t ∈ Subgroup.closure ({lvP lx, lvP lb} : Set Pt)) =>
      ⨆ (_ : t ≠ 1), centDer Xc t) _ heE (le_iSup_of_le he1 le_rfl)
  have hγ := hle (Subgroup.commutator_mem_commutator (comm k1 hk1 h1) (comm k2 hk2 h2))
  have hc1 : (cT k1)⁻¹ = cT k1 := cT_inv dP_sq k1
  have hc2 : (cT k2)⁻¹ = cT k2 := cT_inv dP_sq k2
  have hvi : (selP lx lb vs)⁻¹ = selP lx lb vs := inv_eq_of_mul_eq_one_right hv2
  have e : facP lx lb vs k1 k2 = ⁅selP lx lb vs, ⁅cT k1, cT k2⁆⁆ := by
    unfold facP
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, hvi, hc1, hc2, mul_assoc]
  rw [e]
  exact Subgroup.commutator_mem_commutator hvE hγ

private theorem wP_mem
    {wt : ℕ → ℕ} {lx lb base n : ℕ} (hlx : lx < 262144) (hlb : lb < 262144)
    (hx2 : lvP lx ^ 2 = 1) (hb2 : lvP lb ^ 2 = 1) (hx1 : lvP lx ≠ 1) (hb1 : lvP lb ≠ 1)
    (hxb : lvP lx * lvP lb ≠ 1) (hc : lvP lx * lvP lb = lvP lb * lvP lx)
    (hf : ∀ a < n, facOK gLY TRY wt lx lb base a = true) :
    ∀ m ≤ n, wP wt lx lb base m ∈ nE Xc (Subgroup.closure ({lvP lx, lvP lb} : Set Pt))
  | 0, _ => Subgroup.one_mem _
  | m + 1, hm => by
    obtain ⟨hk1, hk2, h1, h2⟩ := facOK_spec (hf m (by omega))
    exact Subgroup.mul_mem _
      (facP_mem (vs := wt (base + (3 + 2 * m)) % 3) hlx hlb hx2 hb2 hx1 hb1 hxb hc hk1 hk2 h1 h2)
      (wP_mem hlx hlb hx2 hb2 hx1 hb1 hxb hc hf m (by omega))

private theorem wit_monoW
    {wt : ℕ → ℕ} {lx lb base : ℕ} (hlx : lx < 262144) (hlb : lb < 262144)
    (hx2 : lvP lx ^ 2 = 1) (hb2 : lvP lb ^ 2 = 1) (hx1 : lvP lx ≠ 1) (hb1 : lvP lb ≠ 1)
    (hxb : lvP lx * lvP lb ≠ 1) (hc : lvP lx * lvP lb = lvP lb * lvP lx)
    (h : witK gLY TRY wt lx lb base = true) :
    MonoW Xc true (Subgroup.closure ({lvP lx, lvP lb} : Set Pt)) := by
  obtain ⟨hf, h4, h2⟩ := witK_spec h
  have hk : ∀ a < wt (base + 2), wt (base + (4 + 2 * a)) >>> 15 < 31671 ∧
      wt (base + (4 + 2 * a)) &&& 32767 < 31671 := fun a ha => by
    obtain ⟨k1, k2, -⟩ := facOK_spec (hf a ha)
    exact ⟨k1, k2⟩
  have aW := wP_acts hlx hlb hk (wt (base + 2)) le_rfl
  have hW := wP_mem hlx hlb hx2 hb2 hx1 hb1 hxb hc hf (wt (base + 2)) le_rfl
  have hWX : wP wt lx lb base (wt (base + 2)) ∈ Xc := wP_Xc hlx hlb _
  have hit : ∀ n, ∀ b < 6, itN (wY gLY TRY wt lx lb base (wt (base + 2))) n b =
      actN (wP wt lx lb base (wt (base + 2)) ^ n) b := fun n b hb =>
    itN_eq (fun y hy => by rw [actN_eq_val _ hy]; exact (aW y hy).symm) n b (by omega)
  have hW4 : wP wt lx lb base (wt (base + 2)) ^ (4 * wt (base + 1)) = 1 :=
    one_of_fix (Subgroup.pow_mem _ hWX _) fun b hb => by rw [← hit _ b hb]; exact h4 b hb
  have hW2 : wP wt lx lb base (wt (base + 2)) ^ (2 * wt (base + 1)) ≠ 1 := fun e =>
    h2 fun b hb => by rw [hit _ b hb, e, actN_one]
  refine Or.inl ⟨wP wt lx lb base (wt (base + 2)) ^ wt (base + 1), Subgroup.pow_mem _ hW _, ?_⟩
  have hZ2 : ¬ (wP wt lx lb base (wt (base + 2)) ^ wt (base + 1)) ^ 2 ^ 1 = 1 := by
    rw [← pow_mul, pow_one, mul_comm]
    exact hW2
  have hZ4 : (wP wt lx lb base (wt (base + 2)) ^ wt (base + 1)) ^ 2 ^ (1 + 1) = 1 := by
    rw [← pow_mul, show (2 : ℕ) ^ (1 + 1) = 4 by norm_num, mul_comm]
    exact hW4
  rw [orderOf_eq_prime_pow hZ2 hZ4]
  norm_num

theorem facts_of_checks
    {cj wt : ℕ → ℕ} (hR : ∀ i < 3, rootY gLY CDY LS wt i = true)
    (hP : ∀ r < 96, repY CDY wt r = true) (hC : ∀ l < 262144, cenY gLY CDY cj wt l = true)
    (hE : ∀ i < 3, ∀ r < 96, entY gLY TRY CDY wt i r = true) :
    Fi23CensusFactsOn Xc := by
  refine ⟨fun i => lvP (wt (4704 + i)), TY, TY_le, card_TY, fun i hi => ?_,
    fun i hi b hb h2 h1 hbx => ?_⟩
  · obtain ⟨hm, hsq, hne, hfix, hcen, -⟩ := root_facts (hR i hi)
    exact ⟨hm, hsq, hne, hfix, hcen⟩
  obtain ⟨hxm, hx2, hx1, -, hxc, hlx⟩ := root_facts (hR i hi)
  obtain ⟨l, hl, rfl, hcl⟩ := inv_leaf hb h2 h1
  obtain ⟨hr96, ht, hbase⟩ := cen_spec (hC l hl) hcl
  generalize cj l &&& 127 = r at hr96 hbase
  generalize cj l >>> 7 = t at ht hbase
  obtain ⟨hlr, hcr⟩ := rep_spec (hP r hr96)
  have htm := lvP_mem ht
  have htb : lvP t * lvP l = lvP (wt (4608 + r)) * lvP t :=
    eq_base (Subgroup.mul_mem _ htm (lvP_mem hl)) (Subgroup.mul_mem _ (lvP_mem hlr) htm)
      fun y hy => by
        have hy' : y < 31671 := by omega
        rw [actN_mul, actN_mul, ← GL_eq hl hy', ← GL_eq ht (GL_lt hl hy'), ← GL_eq ht hy',
          ← GL_eq hlr (GL_lt ht hy')]
        exact hbase y hy
  have hxt : lvP (wt (4704 + i)) * lvP t = lvP t * lvP (wt (4704 + i)) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hxc (lvP_TY ht))).symm
  have hxb : lvP (wt (4704 + i)) * lvP l = lvP l * lvP (wt (4704 + i)) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hxc hb)).symm
  obtain ⟨hbr2, hbr1, hxbr1, hxbr, hconj⟩ := conj_facts hx2 h2 h1 hbx hxb hxt htb
  rcases ent_cases (hE i hi r hr96) with h0 | hw | ⟨hj, hcj⟩ | ⟨hj, hl', hc', hcj, hb'⟩
  ·
    exfalso
    apply hbx
    rw [h0] at htb
    exact mul_left_cancel (htb.trans hxt)
  ·
    left
    have hw' := wit_monoW hlx hlr hx2 hbr2 hx1 hbr1 hxbr1 hxbr hw
    have e1 : (MulAut.conj (lvP t)⁻¹).toMonoidHom (lvP (wt (4704 + i))) =
        lvP (wt (4704 + i)) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [inv_inv, mul_assoc, hxt, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : (MulAut.conj (lvP t)⁻¹).toMonoidHom (lvP (wt (4608 + r))) = lvP l := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [inv_inv, mul_assoc, ← htb, inv_mul_cancel_left]
    have hι : Function.Injective (MulAut.conj (lvP t)⁻¹).toMonoidHom := by
      simpa only [MulEquiv.coe_toMonoidHom] using (MulAut.conj (lvP t)⁻¹).injective
    have hX : Xc.map (MulAut.conj (lvP t)⁻¹).toMonoidHom = Xc :=
      map_conj_mem (Subgroup.inv_mem _ htm)
    have hEq : (Subgroup.closure ({lvP (wt (4704 + i)), lvP (wt (4608 + r))} : Set Pt)).map
        (MulAut.conj (lvP t)⁻¹).toMonoidHom =
          Subgroup.closure ({lvP (wt (4704 + i)), lvP l} : Set Pt) := by
      rw [MonoidHom.map_closure, Set.image_pair, e1, e2]
    have := (monoW_map_iff (MulAut.conj (lvP t)⁻¹).toMonoidHom hι Xc _ true).2 hw'
    rwa [hX, hEq] at this
  ·
    right
    refine ⟨_, hj, Or.inl ?_⟩
    have e1 : lvP (wt (4608 + r)) = lvP t * lvP l * (lvP t)⁻¹ := by
      rw [htb, mul_inv_cancel_right]
    calc fixP (lvP l) = fixP (lvP (wt (4608 + r))) := by rw [e1, fixP_conj]
      _ = fi23Fix[wt (16 * (96 * i + r) + 1)]! := by rw [fixP_lvP hlr hcr hbr2, hcj]
      _ = _ := (root_facts (hR _ (by omega))).2.2.2.1.symm
  ·
    right
    refine ⟨_, hj, Or.inr ?_⟩
    have hl'eq : lvP (wt (16 * (96 * i + r) + 2)) = lvP (wt (4704 + i)) * lvP (wt (4608 + r)) :=
      eq_base (lvP_mem hl') (Subgroup.mul_mem _ hxm (lvP_mem hlr)) fun y hy => by
        have hy' : y < 31671 := by omega
        rw [actN_mul, ← GL_eq hl' hy', ← GL_eq hlr hy', ← GL_eq hlx (GL_lt hlr hy')]
        exact hb' y hy
    have e1 : lvP (wt (4704 + i)) * lvP (wt (4608 + r)) =
        lvP t * (lvP (wt (4704 + i)) * lvP l) * (lvP t)⁻¹ := by
      rw [hconj, mul_inv_cancel_right]
    have hsq : lvP (wt (16 * (96 * i + r) + 2)) ^ 2 = 1 := by
      rw [hl'eq]
      exact sq_one_of_comm hx2 hbr2 hxbr
    calc fixP (lvP (wt (4704 + i)) * lvP l) = fixP (lvP (wt (16 * (96 * i + r) + 2))) := by
          rw [hl'eq, e1, fixP_conj]
      _ = fi23Fix[wt (16 * (96 * i + r) + 1)]! := by rw [fixP_lvP hl' hc' hsq, hcj]
      _ = _ := (root_facts (hR _ (by omega))).2.2.2.1.symm

end CertificateChecks.KernelFi23Y.KSF

end
