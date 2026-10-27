module

public import Certificates.Kernel.Sporadic.Fi24G2e.Bridge
public import Certificates.Kernel.Sporadic.Fi24Orb.Order
public import Certificates.Kernel.Sporadic.Fi24Orb.Joined
public import Certificates.Kernel.Sporadic.Fi24Orb.Core
public import CFSG.Sporadic.Fi24.PtGraph
public import Certificates.Kernel.Sporadic.Fi24F3d.Kneser
public import Certificates.Kernel.Sporadic.Fi24F3d.Data
import Certificates.Kernel.Sporadic.Fi24F3d.P
import Mathlib.Tactic.Group
public import CFSG.Sporadic.Fi24.Orbit
public import Certificates.Certificate1016Base

public section

namespace CertificateChecks.KernelFi24F3d

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 CertificateChecks.KernelFi24Fix
  CertificateChecks.KernelFi24Orb CertificateChecks.KernelFi24G2e TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb
  CFSG.KC.Fi24OrbS CFSG.KC.Fi24OrbT CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev wq (w : List ℕ) : Fi24AutomorphismGroup := (w.map g0).prod

noncomputable abbrev xw (w : List ℕ) : GL (Fin 781) (ZMod 3) := τ (wq w)

theorem wq_append (u v : List ℕ) : wq (u ++ v) = wq u * wq v := by
  simp only [wq, List.map_append, List.prod_append]

theorem xw_append (u v : List ℕ) : xw (u ++ v) = xw u * xw v := by
  simp only [xw, wq_append, map_mul]

theorem wq_reverse (w : List ℕ) : wq w.reverse = (wq w)⁻¹ := by
  induction w with
  | nil => simp [wq]
  | cons g w ih =>
    rw [List.reverse_cons, wq_append, ih]
    simp [wq, g0_inv]

theorem xw_reverse (w : List ℕ) : xw w.reverse = (xw w)⁻¹ := by
  rw [xw, wq_reverse, map_inv]

theorem wq_mem_E : ∀ w : List ℕ, (∀ g ∈ w, g < 12) → w.length % 2 = 0 → wq w ∈ E
  | [], _, _ => E.one_mem
  | [_], _, h => by simp at h
  | a :: b :: w, hw, h => by
    have hr := wq_mem_E w (fun g hg => hw g (by simp [hg]))
      (by simp only [List.length_cons] at h; omega)
    have hab := pair_mem_E (hw a (by simp)) (hw b (by simp))
    have e : wq (a :: b :: w) = (g0 a * g0 b) * wq w := by simp [wq, mul_assoc]
    rw [e]
    exact E.mul_mem hab hr

theorem seedGrp_eq_Γ : seedGrp = Γ := Jc_eq

theorem xw_mem {w : List ℕ} (hw : ∀ g ∈ w, g < 12) (he : w.length % 2 = 0) :
    xw w ∈ seedGrp := by
  have hq := wq_mem_E w hw he
  have h1 : xw w = σE ⟨wq w, hq⟩ := τ_E ⟨wq w, hq⟩
  obtain ⟨u, hu⟩ := fi24PrimeGroupMulEquivCommutator.surjective (⟨wq w, hq⟩ : E)
  rw [h1, ← hu, σE_iso, seedGrp_eq_Γ]
  exact ⟨u, rfl⟩

theorem act_xw_inv {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {r : ℕ} (hr : r < N) :
    act (xw w)⁻¹ (ψ r) = ψ (walk CFSG.KD.Fi24Fix.TG w r) := (ψ_walk_τ hw hr).symm

theorem act_xw {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {r : ℕ} (hr : r < N) :
    act (xw w) (ψ (walk CFSG.KD.Fi24Fix.TG w r)) = ψ r := by
  rw [← act_xw_inv hw hr, act_act_inv]

theorem subImg_eq (g : GL (Fin 781) (ZMod 3)) (V : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
    subImg g V = act g V := rfl

theorem isPt_iff (V : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : IsPt V ↔ ∃ r < N, ψ r = V := by
  change (∃ g ∈ seedGrp, act g CertificateChecks.KernelFi24Orb.root = V) ↔ V ∈ Ω
  rw [← orbit_Jc]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem isPt_act {c : GL (Fin 781) (ZMod 3)} (hc : c ∈ seedGrp)
    {V : Submodule (ZMod 3) (Fin 781 → ZMod 3)} (hV : IsPt V) : IsPt (act c V) := by
  obtain ⟨g, hg, rfl⟩ := hV
  exact ⟨c * g, seedGrp.mul_mem hc hg, by rw [subImg_eq, act_mul]; rfl⟩

noncomputable abbrev rootA : Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
  CertificateChecks.KernelFi24Orb.root.map (Matrix.mulVecLin CFSG.Sporadic.Fi24.mA)

theorem rootA_eq : rootA = ψ (walk CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.AW (CFSG.KD.Fi24Orb.NM 0)) := by
  rw [ψ_A (NM_lt (by norm_num)), ψ_root, act_uA]

theorem root_eq : CertificateChecks.KernelFi24Orb.root = ψ (CFSG.KD.Fi24Orb.NM 0) := ψ_root.symm

theorem ptAdj_iff_act (V W : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
    PtAdj V W ↔ ∃ g ∈ seedGrp, act g CertificateChecks.KernelFi24Orb.root = V ∧ act g rootA = W := Iff.rfl

theorem ptAdj_irrefl (V : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : ¬ PtAdj V V := by
  rintro ⟨g, -, h1, h2⟩
  have e : CertificateChecks.KernelFi24Orb.root = rootA := act_inj g (h1.trans h2.symm)
  rw [root_eq, rootA_eq] at e
  have := ψ_inj (NM_lt (by norm_num)) (walk_lt (by decide) (NM_lt (by norm_num))) e
  have h := CFSG.KD.Fi24F3d.P.aw
  rw [← this] at h
  exact absurd h (by simp [CFSG.KC.Fi24Kn.negB])

theorem ptAdj_act {c : GL (Fin 781) (ZMod 3)} (hc : c ∈ seedGrp)
    (V W : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : PtAdj (act c V) (act c W) ↔ PtAdj V W := by
  constructor
  · rintro ⟨g, hg, h1, h2⟩
    refine ⟨c⁻¹ * g, seedGrp.mul_mem (seedGrp.inv_mem hc) hg, ?_, ?_⟩
    · rw [subImg_eq, act_mul]
      change act c⁻¹ (act g CertificateChecks.KernelFi24Orb.root) = V
      rw [show act g CertificateChecks.KernelFi24Orb.root = act c V from h1, act_inv_act]
    · rw [subImg_eq, act_mul]
      change act c⁻¹ (act g rootA) = W
      rw [show act g rootA = act c W from h2, act_inv_act]
  · rintro ⟨g, hg, h1, h2⟩
    refine ⟨c * g, seedGrp.mul_mem hc hg, ?_, ?_⟩
    · rw [subImg_eq, act_mul]
      change act c (act g CertificateChecks.KernelFi24Orb.root) = act c V
      rw [show act g CertificateChecks.KernelFi24Orb.root = V from h1]
    · rw [subImg_eq, act_mul]
      change act c (act g rootA) = act c W
      rw [show act g rootA = W from h2]

def Δ : Set (Submodule (ZMod 3) (Fin 781 → ZMod 3)) :=
  {W | ∃ h ∈ seedGrp, act h CertificateChecks.KernelFi24Orb.root = CertificateChecks.KernelFi24Orb.root ∧ act h rootA = W}

theorem Δ_eq_orbit : Δ = MulAction.orbit (MulAction.stabilizer Jc CertificateChecks.KernelFi24Orb.root) rootA := by
  ext W
  constructor
  · rintro ⟨h, hh, h1, rfl⟩
    exact ⟨⟨⟨h, hh⟩, h1⟩, rfl⟩
  · rintro ⟨⟨⟨h, hh⟩, h1⟩, rfl⟩
    exact ⟨h, hh, h1, rfl⟩

theorem ncard_Δ_dvd : Δ.ncard ∣ 4089470473293004800 := by
  have hfin : Finite (MulAction.stabilizer Jc CertificateChecks.KernelFi24Orb.root) :=
    Nat.finite_of_card_ne_zero (by rw [card_stab_Jc]; norm_num)
  rw [Δ_eq_orbit, ← MulAction.index_stabilizer, ← card_stab_Jc]
  exact Subgroup.index_dvd_card _

theorem C0_lt : ∀ g ∈ CFSG.KD.Fi24F3d.C0, g < 12 := by decide

theorem C0_even : CFSG.KD.Fi24F3d.C0.length % 2 = 0 := by decide

noncomputable abbrev u0 : GL (Fin 781) (ZMod 3) := xw CFSG.KD.Fi24F3d.C0

theorem u0_mem : u0 ∈ seedGrp := xw_mem C0_lt C0_even

theorem walk_C0_root : walk CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24F3d.C0 (CFSG.KD.Fi24Orb.NM 0) = 0 :=
  Nat.eq_of_beq_eq_true CFSG.KD.Fi24F3d.P.root

theorem u0_V0 : act u0 (ψ 0) = CertificateChecks.KernelFi24Orb.root := by
  rw [← walk_C0_root, act_xw C0_lt (NM_lt (by norm_num)), root_eq]

theorem u0_inv_root : act u0⁻¹ CertificateChecks.KernelFi24Orb.root = ψ 0 := by
  rw [← u0_V0, act_inv_act]

theorem u0_s1 : act u0 (ψ 6983) = rootA := by
  rw [← Nat.eq_of_beq_eq_true CFSG.KD.Fi24F3d.P.s1,
    act_xw C0_lt (walk_lt (by decide) (NM_lt (by norm_num))), rootA_eq]

def Pr (x : ℕ) : Prop := act u0 (ψ x) ∈ Δ

theorem Pr_tk {k p : ℕ} (hk : k < 10) (hk8 : k ≠ 8) (hp : p < N) :
    Pr (tk CFSG.KD.Fi24Fix.TG k p) ↔ Pr p := by
  unfold Pr
  rw [ψ_tk (by omega) hp]
  set z := u0 * (xs k)⁻¹ * u0⁻¹ with hz
  have hzm : z ∈ seedGrp := by
    refine seedGrp.mul_mem (seedGrp.mul_mem u0_mem ?_) (seedGrp.inv_mem u0_mem)
    rw [seedGrp_eq_Γ]
    exact Γ.inv_mem (xs_mem k)
  have hV : act (xs k)⁻¹ V0 = V0 := mem_stab.1 ((stab V0).inv_mem (h0_stab hk hk8))
  have hzr : act z CertificateChecks.KernelFi24Orb.root = CertificateChecks.KernelFi24Orb.root := by
    rw [hz, act_mul, act_mul, u0_inv_root, ψ_zero, hV, ← ψ_zero, u0_V0]
  have e : act u0 (act (xs k)⁻¹ (ψ p)) = act z (act u0 (ψ p)) := by
    rw [hz, act_mul, act_mul, act_inv_act]
  rw [e]
  constructor
  · rintro ⟨h, hh, h1, h2⟩
    refine ⟨z⁻¹ * h, seedGrp.mul_mem (seedGrp.inv_mem hzm) hh, ?_, ?_⟩
    · rw [act_mul, h1]
      exact act_inv_eq_of_act_eq hzr
    · rw [act_mul, h2, act_inv_act]
  · rintro ⟨h, hh, h1, h2⟩
    refine ⟨z * h, seedGrp.mul_mem hzm hh, ?_, ?_⟩
    · rw [act_mul, h1, hzr]
    · rw [act_mul, h2]

theorem Pr_6983 : Pr 6983 := ⟨1, seedGrp.one_mem, act_one _, by rw [act_one, u0_s1]⟩

theorem comp_6983 : fComp (CFSG.KD.Fi24Orb.FD 6983) = 2 :=
  Nat.eq_of_beq_eq_true CFSG.KD.Fi24F3d.P.c1

theorem Pr_closed {i : ℕ} (hi1 : 1 ≤ i) (hin : i < N) (hPi : Pr i) :
    ∀ r, 1 ≤ r → r < N → fComp (CFSG.KD.Fi24Orb.FD r) = fComp (CFSG.KD.Fi24Orb.FD i) → Pr r :=
  forest_closed CFSG.KD.Fi24Orb.forest_all Pr (fun k p hk hk8 _ hp => Pr_tk hk hk8 hp) hi1 hin hPi

theorem Pr_of_comp2 {x : ℕ} (h1 : 1 ≤ x) (hx : x < N)
    (hc : fComp (CFSG.KD.Fi24Orb.FD x) = 2) : Pr x :=
  Pr_closed (by norm_num) (by norm_num) Pr_6983 x h1 hx (by rw [hc, comp_6983])

theorem Δ_sub_Ω : Δ ⊆ Ω := by
  rintro _ ⟨h, hh, -, rfl⟩
  have hA : IsPt rootA := ⟨uA, uA_Jc, act_uA CertificateChecks.KernelFi24Orb.root⟩
  exact (isPt_iff _).1 (isPt_act hh hA)

theorem Ω_finite : Ω.Finite := by
  have e : Ω = ((Finset.range N).image ψ : Set _) := by
    ext W
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  rw [e]
  exact Finset.finite_toSet _

theorem not_Pr_of_comp1 {x : ℕ} (h1 : 1 ≤ x) (hx : x < N)
    (hc : fComp (CFSG.KD.Fi24Orb.FD x) = 1) : ¬ Pr x := by
  intro hPx
  have hall : ∀ r, 1 ≤ r → r < N → Pr r := by
    intro r hr1 hrN
    rcases (CFSG.KD.Fi24Orb.forest_all r hr1 hrN).1 with h | ⟨h, -⟩
    · exact Pr_closed h1 hx hPx r hr1 hrN (by rw [h, hc])
    · exact Pr_of_comp2 hr1 hrN h
  have hsub : ((Finset.Icc 1 (N - 1)).image fun r => act u0 (ψ r) : Set _) ⊆ Δ := by
    intro W hW
    simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc] at hW
    obtain ⟨r, ⟨hr1, hr2⟩, rfl⟩ := hW
    exact hall r hr1 (by omega)
  have hinj : Set.InjOn (fun r => act u0 (ψ r)) (Finset.Icc 1 (N - 1) : Set ℕ) := by
    intro r hr r' hr' e
    simp only [Finset.coe_Icc, Set.mem_Icc] at hr hr'
    exact ψ_inj (by omega) (by omega) (act_inj u0 e)
  have hge : N - 1 ≤ Δ.ncard := by
    have h1 := Set.ncard_le_ncard hsub (Ω_finite.subset Δ_sub_Ω)
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at h1
    simpa using h1
  have hle : Δ.ncard ≤ N := by
    rw [← ncard_Ω]
    exact Set.ncard_le_ncard Δ_sub_Ω Ω_finite
  have hd := ncard_Δ_dvd
  have hcases : Δ.ncard = 306935 ∨ Δ.ncard = 306936 := by
    simp only [N] at hge hle
    omega
  rcases hcases with h | h <;> rw [h] at hd <;> norm_num at hd

theorem ptAdj_iff {r s : ℕ} (hr : r < N) (hs : s < N) (hrs : r ≠ s) {c : List ℕ}
    (hc : ∀ g ∈ c, g < 12) (he : c.length % 2 = 0) (h0 : walk CFSG.KD.Fi24Fix.TG c r = 0) :
    PtAdj (ψ r) (ψ s) ↔ fComp (CFSG.KD.Fi24Orb.FD (walk CFSG.KD.Fi24Fix.TG c s)) = 2 := by
  set t := walk CFSG.KD.Fi24Fix.TG c s with ht
  have htN : t < N := walk_lt hc hs
  have hr0 : act (xw c)⁻¹ (ψ r) = ψ 0 := by rw [act_xw_inv hc hr, h0]
  have hst : act (xw c)⁻¹ (ψ s) = ψ t := act_xw_inv hc hs
  have ht0 : t ≠ 0 := by
    intro h
    apply hrs
    apply ψ_inj hr hs
    apply act_inj (xw c)⁻¹
    rw [hr0, hst, h]
  have hcm := xw_mem hc he
  have key : PtAdj (ψ r) (ψ s) ↔ Pr t := by
    rw [ptAdj_iff_act]
    constructor
    · rintro ⟨g, hg, h1, h2⟩
      refine ⟨u0 * (xw c)⁻¹ * g, seedGrp.mul_mem (seedGrp.mul_mem u0_mem (seedGrp.inv_mem hcm)) hg,
        ?_, ?_⟩
      · rw [act_mul, act_mul, h1, hr0, u0_V0]
      · rw [act_mul, act_mul, h2, hst]
    · rintro ⟨h, hh, h1, h2⟩
      refine ⟨xw c * u0⁻¹ * h, seedGrp.mul_mem (seedGrp.mul_mem hcm (seedGrp.inv_mem u0_mem)) hh,
        ?_, ?_⟩
      · rw [act_mul, act_mul, h1, u0_inv_root, ← hr0, act_act_inv]
      · rw [act_mul, act_mul, h2, act_inv_act, ← hst, act_act_inv]
  rw [key]
  constructor
  · intro hP
    rcases (CFSG.KD.Fi24Orb.forest_all t (by omega) htN).1 with h | ⟨h, -⟩
    · exact absurd hP (not_Pr_of_comp1 (by omega) htN h)
    · exact h
  · exact Pr_of_comp2 (by omega) htN

theorem mem_ptFix {g : GL (Fin 781) (ZMod 3)} {V : Submodule (ZMod 3) (Fin 781 → ZMod 3)} :
    V ∈ ptFix g ↔ IsPt V ∧ act g V = V := Iff.rfl

theorem act_inv_eq_iff {g : GL (Fin 781) (ZMod 3)} {V : Submodule (ZMod 3) (Fin 781 → ZMod 3)} :
    act g⁻¹ V = V ↔ act g V = V := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact act_act_inv g V
  · exact act_inv_eq_of_act_eq

theorem ptFix_inv (g : GL (Fin 781) (ZMod 3)) : ptFix g⁻¹ = ptFix g := by
  ext V
  rw [mem_ptFix, mem_ptFix, act_inv_eq_iff]

theorem act_pow_of_act {g : GL (Fin 781) (ZMod 3)} {V : Submodule (ZMod 3) (Fin 781 → ZMod 3)}
    (h : act g V = V) : ∀ n : ℕ, act (g ^ n) V = V
  | 0 => by rw [pow_zero, act_one]
  | n + 1 => by rw [pow_succ, act_mul, h, act_pow_of_act h n]

theorem ptFix_pow5 {g : GL (Fin 781) (ZMod 3)} (h5 : g ^ 5 = 1) {j : ℕ} (hj0 : 0 < j) (hj : j < 5) :
    ptFix (g ^ j) = ptFix g := by
  have hinv : ∃ j' : ℕ, (g ^ j) ^ j' = g := by
    interval_cases j
    · exact ⟨1, by rw [pow_one, pow_one]⟩
    · exact ⟨3, by rw [← pow_mul, show 2 * 3 = 5 + 1 by rfl, pow_add, h5, one_mul, pow_one]⟩
    · exact ⟨2, by rw [← pow_mul, show 3 * 2 = 5 + 1 by rfl, pow_add, h5, one_mul, pow_one]⟩
    · exact ⟨4, by rw [← pow_mul, show 4 * 4 = 5 * 3 + 1 by rfl, pow_add, pow_mul, h5, one_pow,
        one_mul, pow_one]⟩
  obtain ⟨j', hj'⟩ := hinv
  ext V
  rw [mem_ptFix, mem_ptFix]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    have := act_pow_of_act h j'
    rwa [hj'] at this
  · rintro ⟨hp, h⟩
    exact ⟨hp, act_pow_of_act h j⟩

@[expose] def KnModel (g : GL (Fin 781) (ZMod 3)) (n : ℕ) : Prop :=
  ∃ φ : ptFix g ≃ KP n, ∀ V W : ptFix g, PtAdj V W ↔ KP.Disj (φ V) (φ W)

theorem KnModel.ofEq {g h : GL (Fin 781) (ZMod 3)} {n : ℕ} (e : ptFix g = ptFix h)
    (M : KnModel g n) : KnModel h n := by
  unfold KnModel
  rw [← e]
  exact M

noncomputable def ptFixConj {g c : GL (Fin 781) (ZMod 3)} (hc : c ∈ seedGrp) :
    ptFix (c⁻¹ * g * c) ≃ ptFix g where
  toFun V := ⟨act c V, isPt_act hc V.2.1, by
    have h : act (c⁻¹ * g * c) V = V := V.2.2
    rw [act_mul, act_mul] at h
    change act g (act c V) = act c V
    conv_rhs => rw [← h]
    rw [act_act_inv]⟩
  invFun W := ⟨act c⁻¹ W, isPt_act (seedGrp.inv_mem hc) W.2.1, by
    have h : act g W = W := W.2.2
    change act (c⁻¹ * g * c) (act c⁻¹ W) = act c⁻¹ W
    rw [act_mul, act_mul, act_act_inv, h]⟩
  left_inv V := Subtype.ext (act_inv_act c V)
  right_inv W := Subtype.ext (act_act_inv c W)

theorem KnModel.conj {g c : GL (Fin 781) (ZMod 3)} {n : ℕ} (hc : c ∈ seedGrp)
    (M : KnModel g n) : KnModel (c⁻¹ * g * c) n := by
  obtain ⟨φ, hφ⟩ := M
  refine ⟨(ptFixConj hc).trans φ, fun V W => ?_⟩
  rw [Equiv.trans_apply, Equiv.trans_apply, ← hφ]
  exact (ptAdj_act hc V W).symm

theorem knModel_of_data {w : List ℕ} (hw : ∀ g ∈ w, g < 12)
    {L A B : ℕ → ℕ} {C : ℕ → List ℕ} {n m : ℕ} (hm : Fintype.card (KP n) = m)
    (hfix : ∀ r < N, walk CFSG.KD.Fi24Fix.TG w r = r ↔ ∃ j < m, L j = r)
    (hL : ∀ j < m, L j < N ∧ (j + 1 < m → L j < L (j + 1)))
    (hC : ∀ i < m, (∀ g ∈ C i, g < 12) ∧ (C i).length % 2 = 0)
    (hk : ∀ i < m, ∀ j < m, (i = j → walk CFSG.KD.Fi24Fix.TG (C i) (L i) = 0 ∧ A i < B i ∧ B i < n) ∧
      (i ≠ j → ¬ (A i = A j ∧ B i = B j) ∧
        (fComp (CFSG.KD.Fi24Orb.FD (walk CFSG.KD.Fi24Fix.TG (C i) (L j))) = 2 ↔
          A i ≠ A j ∧ A i ≠ B j ∧ B i ≠ A j ∧ B i ≠ B j))) :
    KnModel (xw w) n := by
  have mono : ∀ i j, i < j → j < m → L i < L j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have h1 := (hL j (by omega)).2 (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact (ih h (by omega)).trans h1
      · rw [h]
        exact h1
  have Linj : ∀ i j : Fin m, L i = L j → i = j := by
    intro i j e
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact absurd e (mono _ _ h j.2).ne
    · exact Fin.ext h
    · exact absurd e (mono _ _ h i.2).ne'
  have hfixL : ∀ j < m, walk CFSG.KD.Fi24Fix.TG w (L j) = L j := fun j hj =>
    (hfix (L j) (hL j hj).1).2 ⟨j, hj, rfl⟩
  let f : Fin m → ptFix (xw w) := fun j => ⟨ψ (L j), (isPt_iff _).2 ⟨L j, (hL j j.2).1, rfl⟩, by
    change act (xw w) (ψ (L j)) = ψ (L j)
    conv_lhs => rw [← hfixL j j.2]
    exact act_xw hw (hL j j.2).1⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j e => Linj i j (ψ_inj (hL i i.2).1 (hL j j.2).1 (congrArg Subtype.val e)), ?_⟩
    rintro ⟨V, hp, hV⟩
    obtain ⟨r, hr, rfl⟩ := (isPt_iff V).1 hp
    have h1 : act (xw w)⁻¹ (ψ r) = ψ r := act_inv_eq_iff.2 hV
    rw [act_xw_inv hw hr] at h1
    have h2 := ψ_inj (walk_lt hw hr) hr h1
    obtain ⟨j, hj, rfl⟩ := (hfix r hr).1 h2
    exact ⟨⟨j, hj⟩, rfl⟩
  have hAB : ∀ j : Fin m, A j < B j ∧ B j < n := fun j => ((hk j j.2 j j.2).1 rfl).2
  let lab : Fin m → KP n := fun j =>
    ⟨(⟨A j, by have := hAB j; omega⟩, ⟨B j, (hAB j).2⟩), by
      change A j < B j
      exact (hAB j).1⟩
  have hlab : Function.Bijective lab := by
    refine (Fintype.bijective_iff_injective_and_card lab).2 ⟨fun i j e => ?_, by simp [hm]⟩
    by_contra hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    apply ((hk i i.2 j j.2).2 hne).1
    have e1 := congrArg (fun p : KP n => p.1.1.val) e
    have e2 := congrArg (fun p : KP n => p.1.2.val) e
    exact ⟨e1, e2⟩
  let eF := Equiv.ofBijective f hf
  let eL := Equiv.ofBijective lab hlab
  refine ⟨eF.symm.trans eL, fun V W => ?_⟩
  obtain ⟨i, rfl⟩ := eF.surjective V
  obtain ⟨j, rfl⟩ := eF.surjective W
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  change PtAdj (ψ (L i)) (ψ (L j)) ↔ KP.Disj (lab i) (lab j)
  by_cases hij : i = j
  · subst hij
    exact iff_of_false (ptAdj_irrefl _) (KP.disj_irrefl _)
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hLne : L i ≠ L j := fun e => hij (Linj i j e)
    obtain ⟨h0, -⟩ := (hk i i.2 i i.2).1 rfl
    rw [ptAdj_iff (hL i i.2).1 (hL j j.2).1 hLne (hC i i.2).1 (hC i i.2).2 h0,
      ((hk i i.2 j j.2).2 hne).2]
    unfold KP.Disj
    simp only [lab, ne_eq, Fin.mk.injEq]

theorem KnModel.card {g : GL (Fin 781) (ZMod 3)} {n : ℕ} (M : KnModel g n) :
    Nat.card (ptFix g) = Fintype.card (KP n) := by
  obtain ⟨φ, -⟩ := M
  rw [Nat.card_congr φ, Nat.card_eq_fintype_card]

end CertificateChecks.KernelFi24F3d

end
