module

public import Certificates.Kernel.LyGlue.Facts6

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

theorem conj_of_eq {G : Type*} [Group G] {P A C : G} (h : P * A = C * P) : P * A * P⁻¹ = C := by
  rw [h]
  group

theorem txG_conj (hM : Ly0.ModelChecks) (hxeq : Ly0.xG = Xu) (hyeq : Ly0.y0G = Yu)
    (hweq : Ly0.w0G = Wu) {k : Nat} (hk : k < 4) :
    ∀ e ∈ ({Ly0.xG, Ly0.y0G, Ly0.w0G} : Set (Perm (Fin Ly0.deg))),
      Glue.txG k * e * (Glue.txG k)⁻¹ ∈ Glue.A30p := by
  have h := hM.tab
  have mx : Ly0.xG ∈ Glue.A30p := subset_closure (Set.mem_insert _ _)
  have my : Yu ∈ Glue.A30p := hyeq ▸ subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have mw : Wu ∈ Glue.A30p :=
    hweq ▸ subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have p0 := prodP_tx h (k := 0) (by norm_num)
  have p1 := prodP_tx h (k := 1) (by norm_num)
  have p2 := prodP_tx h (k := 2) (by norm_num)
  have p3 := prodP_tx h (k := 3) (by norm_num)
  intro e he
  rcases he with rfl | rfl | rfl
  · rcases Ly0.conj_xB hM ⟨Glue.txG k, Glue.txG_mem_B0 hk⟩ with hc | hc
    · have hc' := congrArg Subtype.val hc
      change Glue.txG k * Ly0.xG * (Glue.txG k)⁻¹ = Ly0.xG at hc'
      rw [hc']
      exact mx
    · have hc' := congrArg Subtype.val hc
      change Glue.txG k * Ly0.xG * (Glue.txG k)⁻¹ = Ly0.xG⁻¹ at hc'
      rw [hc']
      exact inv_mem mx
  · rw [hyeq]
    interval_cases k
    · rw [conj_of_eq (conj_perm hM (j := 1) (by norm_num) p0 (prodP_y h) (prodP_w2 h) p0)]
      exact mul_mem mw mw
    · rw [conj_of_eq (conj_perm hM (j := 3) (by norm_num) p1 (prodP_y h) (prodP_y2 h) p1)]
      exact mul_mem my my
    · rw [conj_of_eq (conj_perm hM (j := 5) (by norm_num) p2 (prodP_y h) (prodP_y2 h) p2)]
      exact mul_mem my my
    · rw [conj_of_eq (conj_perm hM (j := 7) (by norm_num) p3 (prodP_y h) (prodP_w2 h) p3)]
      exact mul_mem mw mw
  · rw [hweq]
    interval_cases k
    · rw [conj_of_eq (conj_perm hM (j := 2) (by norm_num) p0 (prodP_w h) (prodP_y h) p0)]
      exact my
    · rw [conj_of_eq (conj_perm hM (j := 4) (by norm_num) p1 (prodP_w h) (prodP_w2 h) p1)]
      exact mul_mem mw mw
    · rw [conj_of_eq (conj_perm hM (j := 6) (by norm_num) p2 (prodP_w h) (prodP_w2 h) p2)]
      exact mul_mem mw mw
    · rw [conj_of_eq (conj_perm hM (j := 8) (by norm_num) p3 (prodP_w h) (prodP_y2 h) p3)]
      exact mul_mem my my

theorem txG_mem_Tx' (hM : Ly0.ModelChecks) (hxeq : Ly0.xG = Xu) (hyeq : Ly0.y0G = Yu)
    (hweq : Ly0.w0G = Wu) {k : Nat} (hk : k < 4) :
    (⟨Glue.txG k, Glue.txG_mem_B0 hk⟩ : Ly0.B0) ∈ Ly0.Tx := by
  have hc := txG_conj hM hxeq hyeq hweq hk
  change (⟨Glue.txG k, Glue.txG_mem_B0 hk⟩ : Ly0.B0) ∈
    normalizer (Subgroup.closure ({Ly0.xB, Ly0.yB, Ly0.wB} : Set Ly0.B0) : Set Ly0.B0)
  refine McLAS.mem_normalizer_closure fun e he => ?_
  rcases he with rfl | rfl | rfl
  · exact (Glue.A30p_mem (hc _ (Set.mem_insert _ _))).2
  · exact (Glue.A30p_mem (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))).2
  · exact (Glue.A30p_mem (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _))))).2

theorem Pxp_sub_le_Tx' (hM : Ly0.ModelChecks) (hxeq : Ly0.xG = Xu) (hyeq : Ly0.y0G = Yu)
    (hweq : Ly0.w0G = Wu) :
    (Subgroup.closure (Glue.txG '' {k | k < 4})).subgroupOf Ly0.B0 ≤ Ly0.Tx := by
  have key : ∀ a ∈ Subgroup.closure (Glue.txG '' {k | k < 4}),
      ∃ ha : a ∈ Ly0.B0, (⟨a, ha⟩ : Ly0.B0) ∈ Ly0.Tx := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨Glue.txG_mem_B0 hk, txG_mem_Tx' hM hxeq hyeq hweq hk⟩
    | one => exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨hxB, hxT⟩ := ihx
      obtain ⟨hyB, hyT⟩ := ihy
      exact ⟨Subgroup.mul_mem _ hxB hyB, Subgroup.mul_mem _ hxT hyT⟩
    | inv x hx ihx =>
      obtain ⟨hxB, hxT⟩ := ihx
      exact ⟨Subgroup.inv_mem _ hxB, Subgroup.inv_mem _ hxT⟩
  intro b hb
  obtain ⟨hB, hT⟩ := key (b : Perm (Fin Ly0.deg)) hb
  exact hT

end CertificateChecks.KernelLy

end
