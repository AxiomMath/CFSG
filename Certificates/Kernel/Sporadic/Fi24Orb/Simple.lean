
module

public import Certificates.Kernel.Sporadic.Fi24Orb.Order
public import CFSG.Sporadic.Th.GroupTheory
public import Certificates.Data.Kernel.Spor.Fi24OrbP
import Certificates.Kernel.Sporadic.Fi24Orb.Small

public section

namespace CertificateChecks.KernelFi24Orb

open CertificateChecks.KernelFi24Fix TauCeti TauCeti.Sporadic CFSG.Sporadic.Bridge
  CFSG.KC.Fi24FixC CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb CFSG.KC.Fi24OrbS CFSG.KC.Fi24OrbT CFSG.KD.Fi24Orb
  CFSG.KS.Mat3

theorem f_mem (k : Fin N) : f k ∈ MulAction.orbit Jc root := by
  rw [orbit_Jc]
  exact ⟨NM k, NM_lt k.isLt, rfl⟩

noncomputable def ptE : Fin N ≃ MulAction.orbit Jc root :=
  Equiv.ofBijective (fun k => ⟨f k, f_mem k⟩) ⟨fun i j h => Fin.ext (f_inj i.isLt j.isLt
    (congrArg Subtype.val h)), fun ⟨W, hW⟩ => by
      rw [orbit_Jc] at hW
      obtain ⟨r, hr, rfl⟩ := hW
      obtain ⟨k, hk, rfl⟩ := NM_surj hr
      exact ⟨⟨k, hk⟩, rfl⟩⟩

noncomputable instance idxJc : MulAction Jc (Fin N) := ptE.mulAction Jc

theorem smul_iff (g : Jc) (i j : Fin N) : g • i = j ↔ act g (f i) = f j := by
  change ptE.symm (g • ptE i) = j ↔ _
  rw [Equiv.symm_apply_eq]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem f_smul (g : Jc) (i : Fin N) : f ((g • i : Fin N) : ℕ) = act g (f i) :=
  ((smul_iff g i (g • i)).1 rfl).symm

instance : MulAction.IsPretransitive Jc (Fin N) where
  exists_smul_eq i j := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Jc (ptE i) (ptE j)
    refine ⟨g, (smul_iff g i j).2 ?_⟩
    exact congrArg Subtype.val hg

theorem NI_lt {r : ℕ} (hr : r < N) : NI r < N := by
  obtain ⟨k, hk, rfl⟩ := NM_surj hr
  rw [NI_NM hk]
  exact hk

theorem NM_NI {r : ℕ} (hr : r < N) : NM (NI r) = r := by
  obtain ⟨k, hk, rfl⟩ := NM_surj hr
  rw [NI_NM hk]

noncomputable def pr {r : ℕ} (hr : r < N) : Fin N := ⟨NI r, NI_lt hr⟩

theorem f_pr {r : ℕ} (hr : r < N) : f (pr hr) = ψ r := by
  rw [f_def]
  change ψ (NM (NI r)) = ψ r
  rw [NM_NI hr]

theorem pr_inj {r r' : ℕ} (hr : r < N) (hr' : r' < N) (h : pr hr = pr hr') : r = r' := by
  have e : NI r = NI r' := congrArg Fin.val h
  rw [← NM_NI hr, ← NM_NI hr', e]

noncomputable def xJ (k : ℕ) : Jc := ⟨xs k, Jc_eq ▸ xs_mem k⟩

theorem xJ_smul_pr {k r : ℕ} (hk : k < 11) (hr : r < N) :
    (xJ k)⁻¹ • pr hr = pr (tk_lt hk hr) := by
  rw [smul_iff, f_pr, f_pr, ψ_tk hk hr, Subgroup.coe_inv]
  rfl

noncomputable def p0 : Fin N := pr (r := 0) (by norm_num)

theorem f_p0 : f p0 = V0 := by rw [p0, f_pr, ψ_zero]

theorem xJ_fix {k : ℕ} (hk : xs k ∈ stab V0) : xJ k • p0 = p0 := by
  rw [smul_iff, f_p0]
  exact mem_stab.1 hk

theorem x10_stab : xs 10 ∈ stab V0 := by
  have h := ψ_tk (k := 10) (r := 0) (by norm_num) (by norm_num)
  rw [Nat.eq_of_beq_eq_true t10, ψ_zero] at h
  have : (xs 10)⁻¹ ∈ stab V0 := h.symm
  simpa using (stab V0).inv_mem this

open Pointwise

theorem stab_set {B : Set (Fin N)} (hB : MulAction.IsBlock Jc B) (hm : p0 ∈ B) {g : Jc}
    (hg : g • p0 = p0) : g • B = B :=
  hB.smul_eq_of_mem hm (by rw [hg]; exact hm)

theorem mem_iff_of_stab {B : Set (Fin N)} {g : Jc} (hg : g • B = B) (x : Fin N) :
    g⁻¹ • x ∈ B ↔ x ∈ B := by
  rw [← Set.mem_smul_set_iff_inv_smul_mem, hg]

instance isPreprimitive : MulAction.IsPreprimitive Jc (Fin N) := by
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base p0 fun {B} hm hB => ?_
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨q, hq, hqm⟩ : ∃ q ∈ B, q ≠ p0 := by
    by_contra hc
    exact hsub fun x hx y hy => by
      rw [Classical.not_not.1 (fun h => hc ⟨x, hx, h⟩), Classical.not_not.1 (fun h => hc ⟨y, hy, h⟩)]
  have hH0 : ∀ k, k < 10 → k ≠ 8 → xJ k • B = B := fun k hk hk8 =>
    stab_set hB hm (xJ_fix (h0_stab hk hk8))
  have h10 : xJ 10 • B = B := stab_set hB hm (xJ_fix x10_stab)
  set P : ℕ → Prop := fun r => ∃ hr : r < N, pr hr ∈ B with hPdef
  have hP : ∀ k p, k < 10 → k ≠ 8 → 1 ≤ p → p < N → (P (tk CFSG.KD.Fi24Fix.TG k p) ↔ P p) := by
    intro k p hk hk8 _ hp
    have ht := tk_lt (by omega : k < 11) hp
    simp only [hPdef]
    constructor
    · rintro ⟨_, h⟩
      refine ⟨hp, ?_⟩
      rw [← xJ_smul_pr (by omega) hp] at h
      exact (mem_iff_of_stab (hH0 k hk hk8) _).1 h
    · rintro ⟨_, h⟩
      refine ⟨ht, ?_⟩
      rw [← xJ_smul_pr (by omega) hp]
      exact (mem_iff_of_stab (hH0 k hk hk8) _).2 h
  have hqN : NM q < N := NM_lt q.isLt
  have hq1 : 1 ≤ NM q := by
    rcases Nat.eq_zero_or_pos (NM q) with h0 | h0
    · exfalso
      apply hqm
      apply Fin.ext
      change q.val = NI 0
      rw [← h0, NI_NM q.isLt]
    · exact h0
  have hPq : P (NM q) := ⟨hqN, by
    have : pr hqN = q := Fin.ext (NI_NM q.isLt)
    rw [this]
    exact hq⟩
  have hcl := forest_closed forest_all P hP hq1 hqN hPq
  obtain ⟨he11, he12⟩ := andB_true e1
  obtain ⟨he21, he22⟩ := andB_true e2
  have h8 : xJ 8 • B = B := by
    have key : ∀ e, e < N → P e → P (tk CFSG.KD.Fi24Fix.TG 8 e) → xJ 8 • B = B := by
      rintro e he ⟨_, h1⟩ ⟨_, h2⟩
      rw [← xJ_smul_pr (by norm_num) he] at h2
      have := hB.smul_eq_of_mem h1 h2
      conv_lhs => rw [← this]
      exact smul_inv_smul _ _
    rcases (forest_all (NM q) hq1 hqN).1 with hc | ⟨hc, -⟩
    · have h2 : P 2 := hcl 2 (by norm_num) (by norm_num)
        (by rw [Nat.eq_of_beq_eq_true he11, hc])
      refine key 2 (by norm_num) h2 ?_
      rw [Nat.eq_of_beq_eq_true he12]
      exact h2
    · have h7 : P 718 := hcl 718 (by norm_num) (by norm_num)
        (by rw [Nat.eq_of_beq_eq_true he21, hc])
      refine key 718 (by norm_num) h7 ?_
      have hlt := tk_lt (k := 8) (r := 718) (by norm_num) (by norm_num)
      rcases Nat.eq_zero_or_pos (tk CFSG.KD.Fi24Fix.TG 8 718) with h0 | hpos
      · exact ⟨hlt, by
          have : pr hlt = p0 := by
            apply Fin.ext
            change NI _ = NI 0
            rw [h0]
          rw [this]
          exact hm⟩
      · exact hcl _ hpos hlt (by rw [Nat.eq_of_beq_eq_true he22, hc])
  have hall : ∀ k < 11, xJ k • B = B := by
    intro k hk
    by_cases h8' : k = 8
    · subst h8'
      exact h8
    by_cases h10' : k = 10
    · subst h10'
      exact h10
    · exact hH0 k (by omega) h8'
  have htop : ∀ g : Jc, g • B = B := by
    intro g
    have hmem : g ∈ (MulAction.stabilizer Jc B) := by
      have hJ : (⊤ : Subgroup Jc) = Subgroup.closure (xJ '' Set.Iio 11) := by
        apply Subgroup.map_injective Jc.subtype_injective
        rw [MonoidHom.map_closure, ← Set.image_comp]
        change Subgroup.map Jc.subtype ⊤ = Subgroup.closure ((fun k => xs k) '' Set.Iio 11)
        rw [Subgroup.map_top, Subgroup.range_subtype, Jc_eq]
        exact (le_antisymm Γ_le' (cl_le)).trans rfl
      have : g ∈ (⊤ : Subgroup Jc) := Subgroup.mem_top g
      rw [hJ] at this
      refine (Subgroup.closure_le _).2 ?_ this
      rintro _ ⟨k, hk, rfl⟩
      exact hall k hk
    exact hmem
  ext p
  refine ⟨fun _ => Set.mem_univ p, fun _ => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Jc p0 p
  rw [← hg, ← htop g]
  exact Set.smul_mem_smul_set hm

end CertificateChecks.KernelFi24Orb

end
