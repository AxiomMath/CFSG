module

public import Certificates.Kernel.LocalComp.L34FW
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34FWSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import Certificates.Data.GrSLitL34Sec4FWCommCheck
import CFSG.Certificates.Kernel.L34ScanSound

public section

namespace CertificateChecks.KernelLC.L34FW

open CFSG CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.PSL3Four.Native.FWComm
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34FW CertificateChecks.KernelLC
open CertificateChecks.KernelLC.L34Cert CFSG.KC.PermTool

theorem r₁_mul_self_and_ne : r₁ * r₁ = 1 ∧ r₁ ≠ 1 := by
  have h := orderOf_r₁R
  have h1 : r₁R * r₁R = 1 := by rw [← pow_two, ← h, pow_orderOf_eq_one]
  refine ⟨congrArg Subtype.val h1, fun hr => ?_⟩
  have : r₁R = 1 := Subtype.ext hr
  rw [this, orderOf_one] at h
  exact absurd h (by norm_num)

theorem exists_of_mem_invTabs {t : Tab}
    (ht : t ∈ (invTabs).toList) : ∃ y ∈ S, y * y = 1 ∧ y ≠ 1 ∧ TabRep t y := by
  obtain ⟨hs, -, -⟩ := conj_orbit gTabs_cover gTabs_tabs tabRep_r₁ certFacts.orbit₁
  obtain ⟨c, hc, hrep⟩ := hs t ht
  obtain ⟨h2, h1⟩ := r₁_mul_self_and_ne
  refine ⟨c * r₁ * c⁻¹, conj_mem_S hc r₁_mem_S, ?_, ?_, hrep⟩
  · have e : c * r₁ * c⁻¹ * (c * r₁ * c⁻¹) = c * (r₁ * r₁) * c⁻¹ := by group
    rw [e, h2]
    group
  · intro h
    apply h1
    calc r₁ = c⁻¹ * (c * r₁ * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group

theorem exists_mem_invTabs {y : Equiv.Perm (Fin 42)} (hyS : y ∈ S)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) : ∃ t ∈ (invTabs).toList, TabRep t y :=
  (conjClass₁.1 ⟨y, S_le_R hyS⟩).1 (isConj_r₁_of_inner (x := ⟨y, S_le_R hyS⟩) hyS
    (fun h => hy1 (congrArg Subtype.val h)) (Subtype.ext hy2))

theorem invTabs_eq : invTabs = pts 42 6 315 (L34O.T 0) := hO0.1

theorem mem_invTabs {j : ℕ} (hj : j < 315) : unpack 42 6 (L34O.T 0 j) ∈ (invTabs).toList := by
  rw [invTabs_eq, ← CFSG.KC.L34Scan.pts_get' hj]
  exact getElem!_mem (by rw [size_pts]; exact hj)

theorem cn0 {j : ℕ} (hj : j < 315) : canonK 42 6 (mask 6) (42 * 6) (L34O.T 0 j) = true :=
  hOc 0 (by norm_num) j hj

noncomputable def invP (j : ℕ) : Equiv.Perm (Fin 42) :=
  if hj : j < 315 then (exists_of_mem_invTabs (mem_invTabs hj)).choose else 1

theorem invP_spec {j : ℕ} (hj : j < 315) : invP j ∈ S ∧ invP j * invP j = 1 ∧ invP j ≠ 1 ∧
    TabRep (unpack 42 6 (L34O.T 0 j)) (invP j) := by
  unfold invP
  rw [dif_pos hj]
  exact (exists_of_mem_invTabs (mem_invTabs hj)).choose_spec

theorem reach {y : Equiv.Perm (Fin 42)} (hyS : y ∈ S) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    Relation.ReflTransGen
      (fun x y => ∃ a < 315, ∃ b < 315, x = invP a ∧ y = invP b ∧ x * y = y * x) (invP 0) y := by
  obtain ⟨t, ht, hrep⟩ := exists_mem_invTabs hyS hy2 hy1
  rw [invTabs_eq, Array.mem_toList_iff, Array.mem_iff_getElem] at ht
  obtain ⟨j, hj, rfl⟩ := ht
  have hj' : j < 315 := by rwa [size_pts] at hj
  rw [CFSG.KC.L34Scan.pts_getElem hj'] at hrep
  rw [hrep.perm_eq (invP_spec hj').2.2.2]
  exact tree_sound (fun j hj => cn0 hj) (fun j hj => (invP_spec hj).2.2.2) tree_k j hj'

theorem involution_closure (P : Equiv.Perm (Fin 42) → Prop)
    (hP : ∀ x y, x ∈ S → y ∈ S → x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x * y = y * x →
      P x → P y) {x₀ : Equiv.Perm (Fin 42)} (hx₀S : x₀ ∈ S) (hx₀2 : x₀ * x₀ = 1) (hx₀1 : x₀ ≠ 1)
    (h₀ : P x₀) {y : Equiv.Perm (Fin 42)} (hyS : y ∈ S) (hy2 : y * y = 1) (hy1 : y ≠ 1) : P y := by
  have hstep : ∀ {u v}, Relation.ReflTransGen
      (fun x y => ∃ a < 315, ∃ b < 315, x = invP a ∧ y = invP b ∧ x * y = y * x) u v →
      (P u → P v) ∧ (P v → P u) := by
    intro u v h
    induction h with
    | refl => exact ⟨id, id⟩
    | tail _ hbc ih =>
      obtain ⟨a, ha, b, hb, rfl, rfl, e⟩ := hbc
      obtain ⟨aS, a2, a1, -⟩ := invP_spec ha
      obtain ⟨bS, b2, b1, -⟩ := invP_spec hb
      exact ⟨fun hu => hP _ _ aS bS a2 b2 a1 b1 e (ih.1 hu),
        fun hv => ih.2 (hP _ _ bS aS b2 a2 b1 a1 e.symm hv)⟩
  exact (hstep (reach hyS hy2 hy1)).1 ((hstep (reach hx₀S hx₀2 hx₀1)).2 h₀)

theorem tabRep_G {k : ℕ} {g : Equiv.Perm (Fin 42)} (hk : k < 6) (hg : TabRep gTabs[k]! g) :
    TabRep (unpack 42 6 (L34R.G k)) g := by
  rw [← g_eq hk]
  exact hg

theorem le_of_involutions {H : Subgroup (Equiv.Perm (Fin 42))}
    (hH : ∀ y ∈ S, y * y = 1 → y ≠ 1 → y ∈ H) : S ≤ H := by
  obtain ⟨ha, hb, hc, hd, e0, e1, e2⟩ := gen_sound gen_k
  have mem : ∀ {j}, j < 315 → invP j ∈ H := fun hj =>
    hH _ (invP_spec hj).1 (invP_spec hj).2.1 (invP_spec hj).2.2.1
  have r1 : TabRep (unpack 42 6 (L34R.G 0)) g₁ := tabRep_G (by norm_num) tabRep_g₁
  have r2 : TabRep (unpack 42 6 (L34R.G 1)) g₂ := tabRep_G (by norm_num) tabRep_g₂
  have r3 : TabRep (unpack 42 6 (L34R.G 2)) g₃ := tabRep_G (by norm_num) tabRep_g₃
  have rab := (invP_spec ha).2.2.2.comp (invP_spec hb).2.2.2
  rw [comp_eq, compA_unpack (cn0 ha) (cn0 hb), e0] at rab
  rw [← e1] at r2
  rw [← e2] at r3
  unfold S
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [r1.perm_eq rab]
    exact H.mul_mem (mem ha) (mem hb)
  · rw [r2.perm_eq (invP_spec hc).2.2.2]
    exact mem hc
  · rw [r3.perm_eq (invP_spec hd).2.2.2]
    exact mem hd

end CertificateChecks.KernelLC.L34FW

end
