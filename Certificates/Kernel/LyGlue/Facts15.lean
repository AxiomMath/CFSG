module

public import Certificates.Kernel.LyGlue.Facts14
public import Certificates.Kernel.LyGlue.Facts10

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

theorem Hb_le_UY (hY : Ly1080.YOK) : Hb ≤ Ly0.UYperm :=
  (closure_le _).2 (by rintro _ ⟨l, hl, rfl⟩; exact Glue.txyBp_mem_UYperm hY hl)

theorem exists_modelGlue (hM : Ly0.ModelChecks) (hY : Ly1080.YOK)
    (hT : Ly243.trCheck = true) (hcY : Nat.card Ly0.Y0 ≤ 349920)
    (hcT : Nat.card Ly0.Tx ≤ 7776) (hcK : Nat.card Ly0.Txy ≤ 3888) :
    ∃ M : ModelGlue, ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val [] := by
  classical
  obtain ⟨Φy, hΦy1, hΦy3, -, eY, hyeq, hxeq, hweq, hlines⟩ := yIso hM hY hcY
  obtain ⟨Φx, hΦx1, hΦx3, hΦx4⟩ := xIso hM hY hT hcT hxeq hyeq hweq
  have hHU := Hb_le_UY hY
  have hHT : Hb.subgroupOf Ly0.B0 ≤ Ly0.Txy := by
    have key : ∀ a ∈ Hb, ∃ ha : a ∈ Ly0.B0, (⟨a, ha⟩ : Ly0.B0) ∈ Ly0.Txy := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hx
        have hB := Glue.txyBp_mem_B0 hY hl
        refine ⟨hB, mem_Txy_of_lines hB (hlines l hl _ (Set.mem_insert _ _))
          (hlines l hl _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
          (hlines l hl _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
            (Set.mem_singleton _))))⟩
      | one => exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
      | mul x y hx hy ihx ihy =>
        obtain ⟨hxB, hxT⟩ := ihx
        obtain ⟨hyB, hyT⟩ := ihy
        exact ⟨Subgroup.mul_mem _ hxB hyB, Subgroup.mul_mem _ hxT hyT⟩
      | inv x hx ihx =>
        obtain ⟨hxB, hxT⟩ := ihx
        exact ⟨Subgroup.inv_mem _ hxB, Subgroup.inv_mem _ hxT⟩
    intro b hb
    obtain ⟨hB, hT'⟩ := key (b : Perm (Fin Ly0.deg)) hb
    exact hT'
  have himg : ∀ x (hxH : x ∈ Hb), (Φy ⟨x, hHU hxH⟩ : Perm (Fin Ly1080.deg)) ∈ Ly1080.Txy0 := by
    intro x hxH
    induction hxH using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      rw [hΦy3 l hl]
      exact Ly1080.txyG_mem_Txy0 hY hl
    | one =>
      have : (⟨1, hHU (one_mem _)⟩ : ↥Ly0.UYperm) = 1 := rfl
      rw [this, map_one]
      exact one_mem _
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, hHU (mul_mem hx hy)⟩ : ↥Ly0.UYperm) = ⟨x, hHU hx⟩ * ⟨y, hHU hy⟩ := rfl
      rw [this, map_mul]
      exact mul_mem ihx ihy
    | inv x hx ihx =>
      have : (⟨x⁻¹, hHU (inv_mem hx)⟩ : ↥Ly0.UYperm) = (⟨x, hHU hx⟩)⁻¹ := rfl
      rw [this, map_inv]
      exact inv_mem ihx
  have hpre' : ∀ y ∈ closure (Ly1080.txyG '' {l | l < 5}), ∃ x, ∃ hxH : x ∈ Hb,
      (Φy ⟨x, hHU hxH⟩ : Perm (Fin Ly1080.deg)) = y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      exact ⟨_, subset_closure ⟨l, hl, rfl⟩, hΦy3 l hl _⟩
    | one =>
      refine ⟨1, one_mem _, ?_⟩
      have : (⟨1, hHU (one_mem _)⟩ : ↥Ly0.UYperm) = 1 := rfl
      rw [this, map_one]
      rfl
    | mul a b _ _ iha ihb =>
      obtain ⟨x1, h1, e1⟩ := iha
      obtain ⟨x2, h2, e2⟩ := ihb
      refine ⟨x1 * x2, mul_mem h1 h2, ?_⟩
      have : (⟨x1 * x2, hHU (mul_mem h1 h2)⟩ : ↥Ly0.UYperm) = ⟨x1, hHU h1⟩ * ⟨x2, hHU h2⟩ := rfl
      rw [this, map_mul]
      change (Φy ⟨x1, hHU h1⟩ : Perm (Fin Ly1080.deg)) * Φy ⟨x2, hHU h2⟩ = a * b
      rw [e1, e2]
    | inv a _ iha =>
      obtain ⟨x1, h1, e1⟩ := iha
      refine ⟨x1⁻¹, inv_mem h1, ?_⟩
      have : (⟨x1⁻¹, hHU (inv_mem h1)⟩ : ↥Ly0.UYperm) = (⟨x1, hHU h1⟩)⁻¹ := rfl
      rw [this, map_inv]
      change ((Φy ⟨x1, hHU h1⟩ : Perm (Fin Ly1080.deg)))⁻¹ = a⁻¹
      rw [e1]
  have hpre : ∀ y ∈ Ly1080.Txy0, ∃ x, ∃ hxH : x ∈ Hb,
      (Φy ⟨x, hHU hxH⟩ : Perm (Fin Ly1080.deg)) = y :=
    fun y hy => hpre' y (Glue.Txy0_le_closure1080 hY hy)
  have hΦy2 : ∀ (x : Perm (Fin Ly0.deg)) (hx : x ∈ Ly0.UYperm),
      x ∈ Hb ↔ ((Φy ⟨x, hx⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)) ∈ Ly1080.Txy0 := by
    intro x hx
    constructor
    · intro hxH
      exact himg x hxH
    · intro hxT
      obtain ⟨x', hx'H, e⟩ := hpre _ hxT
      have := congrArg Subtype.val (Φy.injective (Subtype.ext e))
      change x' = x at this
      rw [← this]
      exact hx'H
  have hHb : Nat.card ↥Hb = 3888 := by
    rw [← Ly1080.card_Txy0 hY]
    refine Nat.card_eq_of_bijective (fun x => (⟨Φy ⟨x.1, hHU x.2⟩, himg x.1 x.2⟩ :
      ↥Ly1080.Txy0)) ⟨fun x y e => ?_, fun y => ?_⟩
    · have e' := congrArg Subtype.val e
      have := congrArg Subtype.val (Φy.injective (Subtype.ext e'))
      exact Subtype.ext this
    · obtain ⟨x, hxH, e⟩ := hpre y.1 y.2
      exact ⟨⟨x, hxH⟩, Subtype.ext e⟩
  have eT : (closure (Glue.txG '' {k | k < 4})).subgroupOf Ly0.B0 = Ly0.Tx := by
    have hc : Nat.card ((closure (Glue.txG '' {k | k < 4})).subgroupOf Ly0.B0) = 7776 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Glue.Pxp_le_B0).toEquiv]
      exact hΦx4
    exact Subgroup.eq_of_le_of_card_ge (Pxp_sub_le_Tx' hM hxeq hyeq hweq)
      (by rw [hc]; exact hcT)
  have eK : Hb.subgroupOf Ly0.B0 = Ly0.Txy := by
    have hc : Nat.card (Hb.subgroupOf Ly0.B0) = 3888 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Glue.Hb_le_B0 hY)).toEquiv]
      exact hHb
    exact Subgroup.eq_of_le_of_card_ge hHT (by rw [hc]; exact hcK)
  have hmemUY : ∀ b0 : Ly0.B0, b0 ∈ Ly0.Y0 → (b0 : Perm (Fin Ly0.deg)) ∈ Ly0.UYperm := by
    intro b0 hb
    rw [← eY] at hb
    exact hb
  have hmemUT : ∀ b0 : Ly0.B0, b0 ∈ Ly0.Tx →
      (b0 : Perm (Fin Ly0.deg)) ∈ closure (Glue.txG '' {k | k < 4}) := by
    intro b0 hb
    rw [← eT] at hb
    exact hb
  let ιY : ↥Ly0.Y0 ≃* ↥Ly1080.Y0 := (MulEquiv.subgroupCongr eY).symm.trans
    ((Subgroup.subgroupOfEquivOfLe Ly0.UYperm_le_B0).trans Φy)
  let ιT : ↥Ly0.Tx ≃* ↥Ly243.Tx0 := (MulEquiv.subgroupCongr eT).symm.trans
    ((Subgroup.subgroupOfEquivOfLe Glue.Pxp_le_B0).trans Φx)
  have hιY : ∀ (b0 : Ly0.B0) (hb : b0 ∈ Ly0.Y0) (hUY : (b0 : Perm (Fin Ly0.deg)) ∈ Ly0.UYperm),
      (ιY ⟨b0, hb⟩ : Perm (Fin Ly1080.deg)) = (Φy ⟨(b0 : Perm (Fin Ly0.deg)), hUY⟩ :
        Perm (Fin Ly1080.deg)) := fun _ _ _ => rfl
  have hιT : ∀ (b0 : Ly0.B0) (hb : b0 ∈ Ly0.Tx)
      (hUT : (b0 : Perm (Fin Ly0.deg)) ∈ closure (Glue.txG '' {k | k < 4})),
      (ιT ⟨b0, hb⟩ : Perm (Fin Ly243.deg)) = (Φx ⟨(b0 : Perm (Fin Ly0.deg)), hUT⟩ :
        Perm (Fin Ly243.deg)) := fun _ _ _ => rfl
  refine ⟨{
    ιY := ιY
    ιT := ιT
    tx := fun i => ⟨⟨Glue.txG i.val, Glue.txG_mem_B0 i.isLt⟩,
      txG_mem_Tx' hM hxeq hyeq hweq i.isLt⟩
    txW := fun i => Glue.txWords.getD i.val []
    txW_range := fun i => Glue.txWords_getD_range i.isLt
    tx_val := fun i => rfl
    ιY_u := ?_
    ιT_tx := ?_
    K_iff := ?_
    agree := ?_ }, fun i => rfl⟩
  · intro i hi
    have hu : Ly0.uG i ∈ Ly0.UYperm := Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
    have h : Ly0.uB i ∈ Ly0.Y0 := by
      rw [← eY]
      exact hu
    refine ⟨h, ?_⟩
    rw [hιY _ h hu]
    exact hΦy1 i hi hu
  · intro i
    have hmem : Glue.txG i.val ∈ closure (Glue.txG '' {k | k < 4}) :=
      Subgroup.subset_closure ⟨i.val, i.isLt, rfl⟩
    change ((ιT ⟨⟨Glue.txG i.val, Glue.txG_mem_B0 i.isLt⟩,
      txG_mem_Tx' hM hxeq hyeq hweq i.isLt⟩ : ↥Ly243.Tx0) : Perm (Fin Ly243.deg)) = Ly243.gg i.val
    rw [hιT _ _ hmem]
    exact hΦx1 i.val i.isLt hmem
  · intro b
    obtain ⟨b0, hb⟩ := b
    have hUY := hmemUY b0 hb
    have hK : b0 ∈ Ly0.Txy ↔ (b0 : Perm (Fin Ly0.deg)) ∈ Hb := by
      rw [← eK]
      exact Iff.rfl
    change b0 ∈ Ly0.Txy ↔ ((ιY ⟨b0, hb⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)) ∈ Ly1080.Txy0
    rw [hK, hιY b0 hb hUY]
    exact hΦy2 _ hUY
  · intro j b0 hbY hbT hj hyj
    have hUY := hmemUY b0 hbY
    have hUT := hmemUT b0 hbT
    have hmemH : Glue.txyBp j ∈ Ly0.UYperm := Glue.txyBp_mem_UYperm hY hj
    have h3 := hΦy3 j hj hmemH
    rw [hιY b0 hbY hUY] at hyj
    have h4 : (Φy ⟨(b0 : Perm (Fin Ly0.deg)), hUY⟩ : ↥Ly1080.Y0) = Φy ⟨Glue.txyBp j, hmemH⟩ :=
      Subtype.ext (hyj.trans h3.symm)
    have h5 := Φy.injective h4
    have h6 : (b0 : Perm (Fin Ly0.deg)) = Glue.txyBp j := congrArg Subtype.val h5
    have hmemX : Glue.txyBp j ∈ closure (Glue.txG '' {k | k < 4}) := h6 ▸ hUT
    rw [hιT b0 hbT hUT]
    have e : (⟨(b0 : Perm (Fin Ly0.deg)), hUT⟩ : ↥(closure (Glue.txG '' {k | k < 4}))) =
        ⟨Glue.txyBp j, hmemX⟩ := Subtype.ext h6
    rw [e]
    exact hΦx3 j hj hmemX

end CertificateChecks.KernelLy

end
