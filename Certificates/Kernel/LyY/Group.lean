module

public import Certificates.Kernel.LyY.Glue
public import Certificates.Kernel.LyY.Cent
public import Certificates.Kernel.LyY.Orbits
public import Certificates.Kernel.LyTr.Glue
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelY
public import CFSG.Certificates.Kernel.J2Enum.Group

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyY

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2Enum CFSG.KC.LyY
open CFSG.Monster.B.Co2 CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.LyonsSims.Ly1080
open CertificateChecks.KernelLyTr

noncomputable abbrev GY : Subgroup (Perm (Fin 1080)) := Raw.Orb.Gen 1080 yS 2

theorem prep_perm {X XI : Nat} (h : permOK 1080 11 (mask 11) (1080 * 11) X XI = true) :
    Raw.Orb.PRep 1080 11 X (permOfArr 1080 (unpack 1080 11 X)) :=
  Raw.Orb.prep_of_rep (rep_permOfArr (Raw.Orb.isInvA_unpack h)).1

theorem prep_inv {X XI : Nat} (h : invEqK 1080 11 (mask 11) (1080 * 11) X XI = true) :
    Raw.Orb.PRep 1080 11 X (permOfArr 1080 (unpack 1080 11 X)) :=
  Raw.Orb.prep_of_rep (rep_permOfArr (invEqK_sound h).2).1

theorem mem_of_sift {X : Nat} {γ : Perm (Fin 1080)} (hc : canonK 1080 11 (mask 11) (1080 * 11) X = true)
    (hs : siftK 1080 11 (mask 11) (1080 * 11) (pidn 1080 11) YC.LR YC.TRI YC.BP 3 0 X = true)
    (hp : Raw.Orb.PRep 1080 11 X γ) : γ ∈ GY := by
  obtain ⟨γ', h1, h2⟩ :=
    ((GrpPf.group3 binds YC.head YC.hl (by norm_num) YC.hs).2.2.1 X hc).1 hs
  rwa [Raw.Orb.prep_unique hp h2]

theorem yS_get {j : Nat} (hj : j < 8) : yS[j]! = unpack 1080 11 (YC.S j) := binds.2.2.2.2.1 j hj

theorem prep_S {j : Nat} (hj : j < 8) : Raw.Orb.PRep 1080 11 (YC.S j) (permOfArr 1080 yS[j]!) :=
  (Raw.Orb.prep_PS binds ties.2.2.2.2.2 hj).1

theorem S_mem {j : Nat} (hj : j < 8) : permOfArr 1080 yS[j]! ∈ GY := by
  obtain ⟨hk, hH⟩ := Raw.Orb.rawHeadOK_of binds YC.head
  exact Raw.Orb.S_mem_Gen (Raw.Orb.hd_of_head hk hH) j (by simp [yS]; omega)

theorem ug_eq {j : Nat} (hj : j < 4) : ug j = permOfArr 1080 (unpack 1080 11 (UH.F j)) := by
  unfold ug
  rw [uT hj]
  change permOfArr 1080 (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.KS.MulH.tabT (unpack 1080 11 (UH.F j)))) = _
  rw [CFSG.KS.MulH.natArr_tabT (base11.2.2.2.1 j hj).1]

theorem prep_u {j : Nat} (hj : j < 4) : Raw.Orb.PRep 1080 11 (UH.F j) (ug j) := by
  rw [ug_eq hj]
  exact prep_inv (base11.2.2.2.1 j hj).2.2

theorem ug_mem_GY {i : Nat} (hi : i < 4) : ug i ∈ GY := by
  have hs := c_sift
  simp only [bAnd_iff] at hs
  have hc : ∀ j < 4, canonK 1080 11 (mask 11) (1080 * 11) (UH.F j) = true :=
    fun j hj => (base11.2.2.2.1 j hj).1
  interval_cases i
  · rw [ug_eq (by norm_num), ← ties.1, ← yS_get (by norm_num)]
    exact S_mem (by norm_num)
  · exact mem_of_sift (hc 1 (by norm_num)) hs.1 (prep_u (by norm_num))
  · exact mem_of_sift (hc 2 (by norm_num)) hs.2.1 (prep_u (by norm_num))
  · rw [ug_eq (by norm_num), ← ties.2.1, ← yS_get (by norm_num)]
    exact S_mem (by norm_num)

theorem ug_mem_Y0 {i : Nat} (hi : i < 4) : ug i ∈ Y0 := by
  have hsz : uTabs.size = 4 := by simp [uTabs]
  have h := tp_mem_genOf (n := deg) (gs := uTabs.toList) (g := uTabs[i]!) (by
    rw [getElem!_pos uTabs i (by omega)]
    exact Array.getElem_mem_toList _)
  exact h

theorem Y0_gen {g : Perm (Fin 1080)} (hg : g ∈ tp deg '' {x | x ∈ uTabs.toList.toArray}) :
    ∃ i < 4, g = ug i := by
  obtain ⟨T, hT, rfl⟩ := hg
  have hT' : T ∈ uTabs := by simpa using hT
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hT'
  have hsz : uTabs.size = 4 := by simp [uTabs]
  refine ⟨i, by omega, ?_⟩
  unfold ug
  rw [getElem!_pos uTabs i hi]

theorem Y0_eq : Y0 = GY := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun g hg => ?_
    obtain ⟨i, hi, rfl⟩ := Y0_gen hg
    exact ug_mem_GY hi
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    change permOfArr 1080 yS[j]! ∈ Y0
    interval_cases j
    · rw [yS_get (by norm_num), ties.1, ← ug_eq (by norm_num)]
      exact ug_mem_Y0 (by norm_num)
    · rw [yS_get (by norm_num), ties.2.1, ← ug_eq (by norm_num)]
      exact ug_mem_Y0 (by norm_num)

theorem covN_testBit {f : Nat → Nat} : ∀ K p, (covN f K).testBit p = true → ∃ k < K, f k = p
  | 0, p, h => by
    change (0 : Nat).testBit p = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h (by decide)
  | K + 1, p, h => by
    change (covN f K ||| 1 <<< f K).testBit p = true at h
    rw [Nat.testBit_lor, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨k, hk, e⟩ := covN_testBit K p h
      exact ⟨k, by omega, e⟩
    · exact ⟨K, by omega, h⟩

theorem covN_spec {f : Nat → Nat} {K m : Nat} (h : covN f K = 2 ^ m - 1) :
    ∀ p < m, ∃ k < K, f k = p := by
  intro p hp
  apply covN_testBit K p
  rw [h, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact hp

theorem fix_gen (p : Nat) (hp : p < 1080) (h0 : p ≠ 0) :
    ∃ j < 8, pg 11 (mask 11) (YC.S j) 0 = 0 ∧ pg 11 (mask 11) (YC.S j) p ≠ p := by
  have h : (Nat.beq p 0 || !(allN 8 (fun j => !(Nat.beq (pg 11 (mask 11) (YC.S j) 0) 0 &&
      !(Nat.beq (pg 11 (mask 11) (YC.S j) p) p))))) = true := allN_spec c_fix p hp
  by_contra hne
  have hne' : ∀ j < 8, pg 11 (mask 11) (YC.S j) 0 = 0 → pg 11 (mask 11) (YC.S j) p = p :=
    fun j hj e => by_contra fun ne => hne ⟨j, hj, e, ne⟩
  have hall : allN 8 (fun j => !(Nat.beq (pg 11 (mask 11) (YC.S j) 0) 0 &&
      !(Nat.beq (pg 11 (mask 11) (YC.S j) p) p))) = true := by
    rw [Raw.Orb.allN_iff]
    intro j hj
    rw [Raw.Orb.beq_dec, Raw.Orb.beq_dec]
    by_cases e : pg 11 (mask 11) (YC.S j) 0 = 0
    · rw [decide_eq_true e, decide_eq_true (hne' j hj e)]
      rfl
    · rw [decide_eq_false e]
      rfl
  rw [hall, Raw.Orb.beq_dec, decide_eq_false h0] at h
  exact absurd h (by decide)

set_option exponentiation.threshold 2000 in
theorem cent_one (c : Perm (Fin 1080)) (hc : ∀ g ∈ GY, c * g = g * c) : c = 1 := by
  have hcomm : ∀ g ∈ GY, ∀ x, c (g x) = g (c x) := fun g hg x => by
    have := congrArg (fun f : Perm (Fin 1080) => f x) (hc g hg)
    simpa only [Perm.mul_apply] using this
  have h0 : c 0 = 0 := by
    by_contra hne
    have hne' : ((c 0 : Fin 1080) : Nat) ≠ 0 := fun e => hne (Fin.ext e)
    obtain ⟨j, hj, e0, e1⟩ := fix_gen (c 0) (c 0).2 hne'
    have hP := prep_S hj
    have f0 : permOfArr 1080 yS[j]! 0 = 0 := Fin.ext ((hP 0).symm.trans e0)
    have f1 := hcomm _ (S_mem hj) 0
    rw [f0] at f1
    exact e1 ((hP (c 0)).trans (congrArg Fin.val f1.symm))
  ext p
  obtain ⟨k, hk, e⟩ := covN_spec (Nat.eq_of_beq_eq_true c_cov) p p.2
  have hk' : k < rcnt (YC.LR 0) := by rw [ties.2.2.1]; exact hk
  obtain ⟨-, γ, hγ, hP⟩ := (GrpPf.group3 binds YC.head YC.hl (by norm_num) YC.hs).2.1 0
    (by norm_num) k hk'
  have g0 : γ 0 = p := Fin.ext ((hP 0).symm.trans e)
  rw [← g0, hcomm γ hγ 0, h0]
  rfl

theorem center_Y0 : center ↥Y0 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine cent_one _ fun g hg => ?_
  rw [← Y0_eq] at hg
  exact (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨g, hg⟩)).symm

noncomputable def gT (j : Fin 5) : Perm (Fin 1080) := permOfArr 1080 (unpack 1080 11 (R1.GI j))

theorem prep_gT (j : Fin 5) : Raw.Orb.PRep 1080 11 (R1.GI j) (gT j) :=
  prep_perm (allN_spec c_r1 j j.2)

theorem txySize : txyTabs.size = 5 := by
  have hs : txyWords.length = 5 := by decide
  simp [txyTabs, hs]

theorem tp_txy {j : Nat} (hj : j < 5) : tp deg txyTabs[j]! = gT ⟨j, hj⟩ := by
  rw [txy1080T hj]
  change permOfArr 1080 (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.KS.MulH.tabT (unpack 1080 11 (R1.GI j)))) = _
  rw [CFSG.KS.MulH.natArr_tabT (base11.2.2.2.2.1 j hj).1]
  rfl

theorem Txy0_eq : Txy0 = closure (Set.range gT) := by
  refine congrArg Subgroup.closure ?_
  ext g
  constructor
  · rintro ⟨T, hT, rfl⟩
    have hT' : T ∈ txyTabs := by simpa using hT
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT'
    have hj5 : j < 5 := by rw [← txySize]; exact hj
    refine ⟨⟨j, hj5⟩, ?_⟩
    rw [← tp_txy hj5, getElem!_pos txyTabs j hj]
  · rintro ⟨⟨j, hj⟩, rfl⟩
    refine ⟨txyTabs[j]!, ?_, tp_txy hj⟩
    rw [getElem!_pos txyTabs j (by rw [txySize]; exact hj)]
    simp

theorem sigma_eq : sigma0 = permOfArr 1080 (unpack 1080 11 (SG.F 0)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound SG.all (by norm_num) 0 (by norm_num)
  rw [← SG.eq, Nat.mul_zero] at h
  unfold sigma0
  change permOfArr 1080 (CFSG.Sporadic.SmallOddCore.Native.natArr sigmaTab) = _
  unfold sigmaTab
  rw [h]

theorem prep_sigma : Raw.Orb.PRep 1080 11 (SG.F 0) sigma0 := by
  have h := c_sig
  simp only [bAnd_iff] at h
  rw [sigma_eq]
  exact prep_perm h.1

theorem sigma_not_mem : sigma0 ∉ Txy0 := by
  intro hs
  rw [Txy0_eq] at hs
  have h := c_sig
  simp only [bAnd_iff] at h
  have hall : allN 1080 (fun p => Nat.beq (lget TL (pg 11 (mask 11) (SG.F 0) p)) (lget TL p)) =
      true := by
    rw [Raw.Orb.allN_iff]
    intro p hp
    have e := (orbOK_sound prep_gT k_orb ⟨p, hp⟩ (sigma0 ⟨p, hp⟩)).1 ⟨sigma0, hs, rfl⟩
    rw [← prep_sigma ⟨p, hp⟩] at e
    rw [Raw.Orb.beq_dec, decide_eq_true_eq]
    exact e.symm
  rw [hall] at h
  exact absurd h.2 (by decide)

theorem not_inner : ∀ t ∈ Txy0, ¬ ∀ i < 4, t * ug i * t⁻¹ = sigma0 * ug i * sigma0⁻¹ := by
  intro t ht hall
  have hc : sigma0⁻¹ * t = 1 := by
    refine cent_one _ fun g hg => ?_
    have hle : GY ≤ Subgroup.centralizer ({sigma0⁻¹ * t} : Set (Perm (Fin 1080))) := by
      rw [← Y0_eq]
      refine (Subgroup.closure_le _).2 fun u hu => ?_
      obtain ⟨i, hi, rfl⟩ := Y0_gen hu
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      calc sigma0⁻¹ * t * ug i = sigma0⁻¹ * (t * ug i * t⁻¹) * t := by group
        _ = sigma0⁻¹ * (sigma0 * ug i * sigma0⁻¹) * t := by rw [hall i hi]
        _ = ug i * (sigma0⁻¹ * t) := by group
    exact (Subgroup.mem_centralizer_iff.1 (hle hg) _ rfl)
  have e : t = sigma0 := (inv_mul_eq_one.1 hc).symm
  exact sigma_not_mem (e ▸ ht)

end CertificateChecks.KernelLyY

end
