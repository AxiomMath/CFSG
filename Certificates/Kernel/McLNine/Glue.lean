module

public import Certificates.Kernel.McLNine.Chk
public import Certificates.Kernel.Sporadic.OddCore.MNF
public import CFSG.Certificates.Kernel.McLNineSound
public import CFSG.Sporadic.SmallOddCore.McLLocal
public import CFSG.Sporadic.SmallOddCore.McLAut
public import CFSG.LieType.BorelTits.Basic
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.HardMathSupport.Lang.E6Descent.SylowNormal
public import CFSG.HardMathSupport.Lang.E6Descent.FixedElementary

public section

namespace CertificateChecks.KernelSpor.McLNine

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.KS.McLNine CFSG.QuasithinUnique CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Lang.E6Descent CFSG.Open

set_option maxRecDepth 400000

@[expose] noncomputable def g9 (k : Nat) : Equiv.Perm (Fin 275) := tp 275 (mclCentTbl k)

theorem hF9 : ∀ k, 4 ≤ k → k ≤ 6 → PR (McLCT.F k) (g9 k) := by
  intro k h4 h6
  have e : McLCT.F k = MNd.F k := rfl
  rw [e]
  refine ⟨MNd.Fc (by omega), ⟨by simp only [CFSG.KS.Raw.unpack, Array.size_ofFn], fun i => ?_⟩⟩
  have h := rep_tp (MNd.permF (k := k) (by omega)) i.val i.2
  have h2 : ap (mclCentTbl k) i.val = (CFSG.KS.Raw.unpack 275 9 (MNd.F k))[i.val]! := by
    rw [MNd.tabF (by omega), CFSG.KS.MulH.ap_tabT _ (CFSG.KS.MulH.unpack_lt (MNd.Fc (by omega)))]
  rw [← h2, h, idx_of_lt _ i.2]
  rfl

theorem letters_u : ∀ w ∈ mclIndexNineUWords, Letters w := by
  simp only [Letters]
  decide

theorem letters_x : Letters mclIndexNineX := by
  simp only [Letters]
  decide

theorem letters_y : Letters mclIndexNineY := by
  simp only [Letters]
  decide

theorem letters_o : ∀ w ∈ mclIndexNineOrbitWords, Letters w := by
  simp only [Letters]
  decide

@[expose] noncomputable def A9 : Set (Equiv.Perm (Fin 275)) :=
  Set.range fun j : Fin 3 => wP g9 (mclIndexNineUWords.getD j [])

@[expose] def P0 : Fin 275 := ⟨mclIndexNinePoint, by decide⟩

@[expose] noncomputable def X9 : Equiv.Perm (Fin 275) := wP g9 mclIndexNineX

@[expose] noncomputable def Y9 : Equiv.Perm (Fin 275) := wP g9 mclIndexNineY

theorem facts :
    Nat.card (closure A9) = 128 ∧
    Nat.card ↥(closure A9 ⊓ centralizer (closure A9 : Set (Equiv.Perm (Fin 275)))) = 2 ∧
    (∀ u ∈ A9, u P0 = P0 ∧ u * g9 4 = g9 4 * u) ∧
    (∀ q : Fin 275, q ≠ P0 → ∃ u ∈ A9, u q ≠ q) ∧
    (X9 P0 = P0 ∧ Y9 P0 = P0 ∧ X9 * g9 4 = g9 4 * X9 ∧ Y9 * g9 4 = g9 4 * Y9 ∧ X9 ^ 3 = 1 ∧
      Y9 ^ 3 = 1 ∧ X9 * Y9 = Y9 * X9 ∧ X9 ≠ 1 ∧ Y9 ≠ 1 ∧ Y9 ≠ X9 ∧ Y9 ≠ X9 * X9) ∧
    (mclIndexNineOrbitWords.length = mclIndexNineOrbitPoints.length ∧
      (∀ t < mclIndexNineOrbitWords.length,
        (wP g9 (mclIndexNineOrbitWords.getD t []) P0 : Nat) = mclIndexNineOrbitPoints.getD t 0) ∧
      mclIndexNineOrbitPoints.Pairwise (· < ·)) :=
  mcl9K_sound hF9 rfl letters_u letters_x letters_y letters_o (by decide) chk

@[expose] noncomputable def U9gen : Subgroup (Equiv.Perm (Fin 275)) := closure A9

@[expose] noncomputable def U9 : Subgroup ↥mclP := U9gen.subgroupOf mclP

@[expose] noncomputable def P9 : Subgroup ↥mclP :=
  ((MulAction.stabilizer mclCt P0).map (Subgroup.subtype mclCt)).subgroupOf mclP

@[expose] noncomputable def Q9 : Subgroup ↥mclP := (closure {X9, Y9}).subgroupOf mclP

theorem wP_mem_ct
    {w : List Nat} (hw : Letters w) : wP g9 w ∈ mclCt := by
  rw [← mclT0_facts.2.2.1]
  unfold wP
  apply Subgroup.list_prod_mem
  intro z hz
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
  rcases hw l hl with rfl | rfl
  · exact subset_closure ⟨mclCentTbl 5, by simp, rfl⟩
  · exact subset_closure ⟨mclCentTbl 6, by simp, rfl⟩

theorem A9_mem
    {u : Equiv.Perm (Fin 275)} (hu : u ∈ A9) : u ∈ mclCt := by
  obtain ⟨j, rfl⟩ := hu
  refine wP_mem_ct (letters_u _ ?_)
  rw [List.getD_eq_getElem _ _ (by simp [mclIndexNineUWords])]
  exact List.getElem_mem _

theorem U9gen_le_mclCt :
    U9gen ≤ mclCt := by
  rw [U9gen, closure_le]
  intro u hu
  exact A9_mem hu

theorem U9gen_le_mclP :
    U9gen ≤ mclP :=
  U9gen_le_mclCt.trans inf_le_left

theorem U9_card :
    Nat.card U9 = 128 := by
  rw [U9, card_subgroupOf_of_le U9gen_le_mclP]
  exact facts.1

theorem XY_mem_fix :
    X9 ∈ mclCt ∧ Y9 ∈ mclCt ∧ X9 P0 = P0 ∧ Y9 P0 = P0 :=
  ⟨wP_mem_ct letters_x, wP_mem_ct letters_y, facts.2.2.2.2.1.1, facts.2.2.2.2.1.2.1⟩

theorem XY_group : X9 ^ 3 = 1 ∧ Y9 ^ 3 = 1 ∧ Commute X9 Y9 ∧ X9 ≠ 1 ∧ Y9 ≠ 1 ∧ Y9 ≠ X9 ∧
    Y9 ≠ X9 ^ 2 := by
  obtain ⟨-, -, -, -, hx3, hy3, hxy, hx1, hy1, hyx, hyx2⟩ := facts.2.2.2.2.1
  exact ⟨hx3, hy3, hxy, hx1, hy1, hyx, by rw [pow_two]; exact hyx2⟩

theorem Q9_le_P9 :
    Q9 ≤ P9 := by
  obtain ⟨hxmem, hymem, hxfix, hyfix⟩ := XY_mem_fix
  have hxP : X9 ∈ (MulAction.stabilizer mclCt P0).map (Subgroup.subtype mclCt) := by
    refine ⟨⟨X9, hxmem⟩, ?_, rfl⟩
    change (⟨X9, hxmem⟩ : ↥mclCt) • P0 = P0
    simpa using hxfix
  have hyP : Y9 ∈ (MulAction.stabilizer mclCt P0).map (Subgroup.subtype mclCt) := by
    refine ⟨⟨Y9, hymem⟩, ?_, rfl⟩
    change (⟨Y9, hymem⟩ : ↥mclCt) • P0 = P0
    simpa using hyfix
  have hclosure : closure {X9, Y9} ≤
      (MulAction.stabilizer mclCt P0).map (Subgroup.subtype mclCt) := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hxP
    · exact hyP
  intro z hz
  change z.val ∈ closure {X9, Y9} at hz
  change z.val ∈ (MulAction.stabilizer mclCt P0).map (Subgroup.subtype mclCt)
  exact hclosure hz

theorem Q9_card :
    Nat.card Q9 = 9 := by
  obtain ⟨hxmem, hymem, -, -⟩ := XY_mem_fix
  obtain ⟨hx3, hy3, hcomm, hx1, hy1, hyx, hyx2⟩ := XY_group
  have hyx' : Y9 ∉ zpowers X9 :=
    CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne hx3 hy1 hyx hyx2
  have hcard : Nat.card (closure {X9, Y9}) = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx3 hy3 hcomm hx1 hyx'
  have hle : closure {X9, Y9} ≤ mclP := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact (inf_le_left : mclCt ≤ mclP) hxmem
    · exact (inf_le_left : mclCt ≤ mclP) hymem
  rw [Q9, card_subgroupOf_of_le hle]
  exact hcard

theorem Q9_pow_three : ∀ q ∈ Q9, q ^ 3 = 1 := by
  obtain ⟨hx3, hy3, hcomm, hx1, hy1, hyx, hyx2⟩ := XY_group
  let E : CFSG.RankThree.Asc83Table.E9Basis (Equiv.Perm (Fin 275)) :=
    CFSG.RankThree.Asc83Table.E9Basis.ofNe hx3 hy3 hcomm hx1 hy1 hyx hyx2
  intro q hq
  have hq' : (q : Equiv.Perm (Fin 275)) ∈ E.sub := by
    rw [Q9, Subgroup.mem_subgroupOf] at hq
    simpa [E, CFSG.RankThree.Asc83Table.E9Basis.ofNe,
      CFSG.RankThree.Asc83Table.E9Basis.sub] using hq
  obtain ⟨i, j, -, -, hqij⟩ := E.exists_pow_mul_pow hq'
  apply Subtype.ext
  change (q : Equiv.Perm (Fin 275)) ^ 3 = 1
  simp only [E, CFSG.RankThree.Asc83Table.E9Basis.ofNe,
    CFSG.RankThree.Asc83Table.E9Basis.sub] at hqij
  rw [hqij]
  have hpow_comm : Commute (X9 ^ i) (Y9 ^ j) := Commute.pow_right (Commute.pow_left hcomm i) j
  rw [Commute.mul_pow hpow_comm]
  rw [show (X9 ^ i) ^ 3 = 1 by rw [← pow_mul, mul_comm i 3, pow_mul, hx3, one_pow]]
  rw [show (Y9 ^ j) ^ 3 = 1 by rw [← pow_mul, mul_comm j 3, pow_mul, hy3, one_pow]]
  rw [one_mul]

theorem U9_le_P9 :
    U9 ≤ P9 := by
  have hclosure : U9gen ≤ (MulAction.stabilizer mclCt P0).map (Subgroup.subtype mclCt) := by
    rw [U9gen, closure_le]
    intro u hu
    refine ⟨⟨u, A9_mem hu⟩, ?_, rfl⟩
    change (⟨u, A9_mem hu⟩ : ↥mclCt) • P0 = P0
    simpa using (facts.2.2.1 u hu).1
  intro z hz
  change z.val ∈ U9gen at hz
  change z.val ∈ (MulAction.stabilizer mclCt P0).map (Subgroup.subtype mclCt)
  exact hclosure hz

theorem orbit_ge_35 :
    35 ≤ Nat.card (MulAction.orbit mclCt P0) := by
  obtain ⟨hl, hpts, hsort⟩ := facts.2.2.2.2.2
  have hlen : mclIndexNineOrbitWords.length = 35 := rfl
  have hplen : mclIndexNineOrbitPoints.length = 35 := rfl
  have hmem : ∀ t : Fin 35, mclIndexNineOrbitWords.getD t [] ∈ mclIndexNineOrbitWords := by
    intro t
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact t.2)]
    exact List.getElem_mem _
  let f : Fin 35 → MulAction.orbit mclCt P0 := fun t =>
    ⟨wP g9 (mclIndexNineOrbitWords.getD t []) P0, MulAction.mem_orbit_iff.mpr
      ⟨⟨_, wP_mem_ct (letters_o _ (hmem t))⟩, rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : (wP g9 (mclIndexNineOrbitWords.getD a []) P0 : Nat) =
        (wP g9 (mclIndexNineOrbitWords.getD b []) P0 : Nat) := by
      have := congrArg Subtype.val hab
      exact congrArg Fin.val this
    rw [hpts a (by rw [hlen]; exact a.2), hpts b (by rw [hlen]; exact b.2),
      List.getD_eq_getElem _ _ (by rw [hplen]; exact a.2),
      List.getD_eq_getElem _ _ (by rw [hplen]; exact b.2)] at e
    have hpw := List.pairwise_iff_getElem.1 hsort
    apply Fin.ext
    rcases lt_trichotomy a.val b.val with h | h | h
    · exact absurd e (ne_of_lt (hpw _ _ (by rw [hplen]; exact a.2) (by rw [hplen]; exact b.2) h))
    · exact h
    · exact absurd e.symm
        (ne_of_lt (hpw _ _ (by rw [hplen]; exact b.2) (by rw [hplen]; exact a.2) h))
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem P9_card :
    Nat.card P9 = 9 * Nat.card U9 := by
  have h_orbit_ge : 35 ≤ Nat.card (MulAction.orbit mclCt P0) := orbit_ge_35
  haveI : Fintype ↥mclCt :=
    Fintype.ofInjective (Subtype.val : ↥mclCt → Equiv.Perm (Fin 275)) Subtype.val_injective
  haveI : Fintype ↥(MulAction.stabilizer mclCt P0) :=
    Fintype.ofInjective (Subtype.val : ↥(MulAction.stabilizer mclCt P0) → ↥mclCt)
      Subtype.val_injective
  haveI : Fintype ↑(MulAction.orbit mclCt P0) :=
    Fintype.ofInjective (Subtype.val : ↑(MulAction.orbit mclCt P0) → Fin 275)
      Subtype.val_injective
  have h_orbit_stab : Nat.card (MulAction.orbit mclCt P0) *
      Nat.card (MulAction.stabilizer mclCt P0) = 40320 := by
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (G := mclCt) (X := Fin 275) (b := P0)
    have h_nat : Nat.card ↑(MulAction.orbit mclCt P0) *
        Nat.card ↥(MulAction.stabilizer mclCt P0) = Nat.card ↥mclCt := by
      simpa only [Nat.card_eq_fintype_card] using h
    rw [mclT0_facts.2.2.2.1] at h_nat
    exact h_nat
  have hstab_le : Nat.card (MulAction.stabilizer mclCt P0) ≤ 1152 := by
    have h1 : 35 * Nat.card (MulAction.stabilizer mclCt P0) ≤ 40320 := by
      calc
        35 * Nat.card (MulAction.stabilizer mclCt P0)
            ≤ Nat.card (MulAction.orbit mclCt P0) * Nat.card (MulAction.stabilizer mclCt P0) :=
              Nat.mul_le_mul_right _ h_orbit_ge
        _ = 40320 := h_orbit_stab
    omega
  have hle : (MulAction.stabilizer mclCt P0).map (Subgroup.subtype mclCt) ≤ mclP := by
    rintro _ ⟨a, _, rfl⟩
    exact (inf_le_left : mclCt ≤ mclP) a.2
  have hP_card : Nat.card P9 = Nat.card (MulAction.stabilizer mclCt P0) := by
    rw [P9, card_subgroupOf_of_le hle]
    rw [Subgroup.card_map_of_injective (fun a b h => Subtype.ext h)]
  have hP_le : Nat.card P9 ≤ 1152 := by
    rw [hP_card]
    exact hstab_le
  have hU_dvd : 128 ∣ Nat.card P9 := by
    rw [← U9_card]
    exact Subgroup.card_dvd_of_le U9_le_P9
  have hQ_dvd : 9 ∣ Nat.card P9 := by
    rw [← Q9_card]
    exact Subgroup.card_dvd_of_le Q9_le_P9
  have h1152_dvd : 1152 ∣ Nat.card P9 := by
    have hcop : Nat.Coprime 128 9 := by norm_num
    have := hcop.mul_dvd_of_dvd_of_dvd hU_dvd hQ_dvd
    simpa using this
  have hP_pos : 0 < Nat.card P9 := Nat.card_pos
  have hP_ge : 1152 ≤ Nat.card P9 := Nat.le_of_dvd hP_pos h1152_dvd
  have hP_eq : Nat.card P9 = 1152 := le_antisymm hP_le hP_ge
  norm_num [hP_eq, U9_card]

theorem P9_le_C : P9 ≤ mclCt.subgroupOf mclP := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  rw [P9, Subgroup.mem_subgroupOf] at hx
  rcases hx with ⟨a, ha, hxa⟩
  rw [← hxa]
  exact a.2

theorem U9_isSylow_C :
    IsSylowTwoOf U9 (mclCt.subgroupOf mclP) := by
  have hle : U9 ≤ mclCt.subgroupOf mclP := U9_le_P9.trans P9_le_C
  refine ⟨hle, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 7) (by rw [U9_card]; norm_num)
  · have hcard_C : Nat.card (mclCt.subgroupOf mclP) = 40320 := by
      rw [card_subgroupOf_of_le (inf_le_left : mclCt ≤ mclP), mclT0_facts.2.2.2.1]
    have hcard_U : Nat.card (U9.subgroupOf (mclCt.subgroupOf mclP)) = 128 := by
      rw [card_subgroupOf_of_le hle, U9_card]
    have h_mul := Subgroup.card_mul_index (H := U9.subgroupOf (mclCt.subgroupOf mclP))
    rw [hcard_C] at h_mul
    have h_idx : (U9.subgroupOf (mclCt.subgroupOf mclP)).index = 315 := by
      rw [hcard_U] at h_mul
      omega
    rw [h_idx]
    norm_num

theorem U9_fix
    (u : ↥mclP) (hu : u ∈ U9) : u.val P0 = P0 := by
  have huP : u ∈ P9 := U9_le_P9 hu
  rw [P9, Subgroup.mem_subgroupOf] at huP
  rcases huP with ⟨a, ha, hua⟩
  have hfix : a.val P0 = P0 := by
    change a ∈ MulAction.stabilizer mclCt P0 at ha
    rw [MulAction.mem_stabilizer_iff] at ha
    rw [Subgroup.smul_def] at ha
    simpa using ha
  rw [← hua]
  exact hfix

theorem U9_fix_set
    (q : Fin 275) : (∀ u ∈ U9, u.val q = q) ↔ q = P0 := by
  constructor
  · intro hq
    by_contra hne
    obtain ⟨u, hu, hnu⟩ := facts.2.2.2.1 q hne
    have hP : u ∈ mclP := (inf_le_left : mclCt ≤ mclP) (A9_mem hu)
    have huU : (⟨u, hP⟩ : ↥mclP) ∈ U9 := by
      rw [U9, Subgroup.mem_subgroupOf]
      exact subset_closure hu
    exact hnu (hq ⟨u, hP⟩ huU)
  · intro hq u hu
    rw [hq]
    exact U9_fix u hu

theorem U9_center_card :
    Nat.card ↥(U9 ⊓ Subgroup.centralizer (U9 : Set ↥mclP)) = 2 := by
  have hcent_gen : Nat.card ↥(U9gen ⊓
      Subgroup.centralizer (U9gen : Set (Equiv.Perm (Fin 275)))) = 2 := facts.2.1
  have hmapU : U9.map (Subgroup.subtype mclP) = U9gen :=
    Subgroup.map_subgroupOf_eq_of_le U9gen_le_mclP
  have hmap_cent : (Subgroup.centralizer (U9 : Set ↥mclP)).map (Subgroup.subtype mclP) =
      Subgroup.centralizer (U9gen : Set (Equiv.Perm (Fin 275))) ⊓ mclP := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, z.2⟩
      change mclP.subtype z ∈ Subgroup.centralizer (U9gen : Set (Equiv.Perm (Fin 275)))
      change z ∈ Subgroup.centralizer (U9 : Set ↥mclP) at hz
      rw [Subgroup.mem_centralizer_iff] at hz ⊢
      intro y hy
      rw [← hmapU] at hy
      obtain ⟨w, hwU, hwy⟩ := Subgroup.mem_map.mp hy
      rw [← hwy]
      exact congrArg Subtype.val (hz w hwU)
    · rintro ⟨hxcent, hxmclP⟩
      refine ⟨⟨x, hxmclP⟩, ?_, rfl⟩
      change x ∈ Subgroup.centralizer (U9gen : Set (Equiv.Perm (Fin 275))) at hxcent
      rw [Subgroup.mem_centralizer_iff] at hxcent
      change (⟨x, hxmclP⟩ : ↥mclP) ∈ Subgroup.centralizer (U9 : Set ↥mclP)
      rw [Subgroup.mem_centralizer_iff]
      intro w hwU
      apply Subtype.ext
      exact hxcent w.val (by rw [← hmapU]; exact Subgroup.mem_map.mpr ⟨w, hwU, rfl⟩)
  have hcard_map := Subgroup.card_map_of_injective (Subgroup.subtype_injective mclP)
    (K := U9 ⊓ Subgroup.centralizer (U9 : Set ↥mclP))
  rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective mclP), hmapU, hmap_cent,
    ← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left U9gen_le_mclP)] at hcard_map
  rw [hcent_gen] at hcard_map
  exact hcard_map.symm

theorem t0_mem_U9 :
    (⟨mclT0, mclT0_facts.1⟩ : ↥mclP) ∈ U9 := by
  let H : Subgroup ↥mclP := mclCt.subgroupOf mclP
  let g0 : ↥mclP := ⟨mclT0, mclT0_facts.1⟩
  have hg0_mem_H : g0 ∈ H := Subgroup.mem_subgroupOf.mpr mclT0_mem_Ct
  have hcomm : ∀ h ∈ H, h * g0 = g0 * h := by
    intro h hh
    have hcent : h.val ∈ Subgroup.centralizer ({mclT0} : Set (Equiv.Perm (Fin 275))) := by
      have hc : h.val ∈ mclP ⊓ Subgroup.centralizer ({mclT0} : Set (Equiv.Perm (Fin 275))) := by
        simpa only [mclCt] using Subgroup.mem_subgroupOf.mp hh
      exact (Subgroup.mem_inf.mp hc).2
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hcent mclT0 (by simp)).symm
  have hnorm : H ≤ Subgroup.normalizer (Subgroup.zpowers g0 : Set ↥mclP) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hconj : h * g0 ^ k * h⁻¹ = g0 ^ k := by
        rw [← conj_zpow]
        rw [show h * g0 * h⁻¹ = g0 by rw [hcomm h hh]; group]
      rw [hconj]
      exact Subgroup.zpow_mem (Subgroup.zpowers g0) (Subgroup.mem_zpowers g0) k
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hx' : x = h⁻¹ * (h * x * h⁻¹) * h := by group
      rw [hx', ← hk]
      have hconj : h⁻¹ * g0 ^ k * h = g0 ^ k := by
        have hc := conj_zpow (a := h⁻¹) (b := g0) (i := k)
        rw [inv_inv] at hc
        rw [← hc]
        rw [show h⁻¹ * g0 * h = g0 by rw [mul_assoc, ← hcomm h hh]; group]
      rw [hconj]
      exact Subgroup.zpow_mem (Subgroup.zpowers g0) (Subgroup.mem_zpowers g0) k
  have hN_le_pcore : Subgroup.zpowers g0 ≤ pCoreOf 2 H := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ hnorm ?_
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.zpow_mem H hg0_mem_H k
    · have hg02 : orderOf g0 = 2 := by
        rw [Subgroup.orderOf_mk, mclT0_facts.2.1]
      have hcard : Nat.card ↥(Subgroup.zpowers g0) = 2 := by
        rw [Nat.card_zpowers, hg02]
      exact IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hpc_le : pCoreOf 2 H ≤ U9 := IsSylowTwoOf.pCoreOf_le U9_isSylow_C
  exact hpc_le (hN_le_pcore (Subgroup.mem_zpowers g0))

theorem mem_P9_iff (g : ↥mclP) : g ∈ P9 ↔ g.val ∈ mclCt ∧ g.val P0 = P0 := by
  rw [P9, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hga⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def] at ha
    refine ⟨?_, ?_⟩
    · rw [← hga]
      exact a.2
    · rw [← hga]
      simpa using ha
  · rintro ⟨hct, hfix⟩
    refine ⟨⟨g.val, hct⟩, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    simpa using hfix

theorem map_mem_H (α : MulAut ↥mclP) (hα : U9.map α.toMonoidHom = U9) {x : ↥mclP}
    (hx : x ∈ U9 ⊓ Subgroup.centralizer (U9 : Set ↥mclP)) :
    α x ∈ U9 ⊓ Subgroup.centralizer (U9 : Set ↥mclP) := by
  obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact hα ▸ Subgroup.mem_map_of_mem α.toMonoidHom hxU
  · rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro v hv
    rw [← hα] at hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    calc
      α u * α x = α (u * x) := (map_mul α u x).symm
      _ = α (x * u) := by rw [hxC u hu]
      _ = α x * α u := map_mul α x u

theorem t0_mem_H :
    (⟨mclT0, mclT0_facts.1⟩ : ↥mclP) ∈
      U9 ⊓ Subgroup.centralizer (U9 : Set ↥mclP) := by
  refine Subgroup.mem_inf.mpr ⟨t0_mem_U9, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcu : u.val ∈ mclCt := U9gen_le_mclCt hu
  have hcent : u.val ∈ Subgroup.centralizer ({mclT0} : Set (Equiv.Perm (Fin 275))) :=
    (Subgroup.mem_inf.mp hcu).2
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp hcent mclT0 (by simp)).symm

theorem map_t0
    (α : MulAut ↥mclP) (hα : U9.map α.toMonoidHom = U9) :
    α (⟨mclT0, mclT0_facts.1⟩ : ↥mclP) = (⟨mclT0, mclT0_facts.1⟩ : ↥mclP) := by
  let t0 : ↥mclP := ⟨mclT0, mclT0_facts.1⟩
  let H : Subgroup ↥mclP := U9 ⊓ Subgroup.centralizer (U9 : Set ↥mclP)
  have ht0H : t0 ∈ H := t0_mem_H
  have hzH : Subgroup.zpowers t0 ≤ H := Subgroup.zpowers_le.mpr ht0H
  have ht0ord : orderOf t0 = 2 := by
    rw [Subgroup.orderOf_mk, mclT0_facts.2.1]
  have hcard_t0 : Nat.card ↥(Subgroup.zpowers t0) = 2 := by
    rw [Nat.card_zpowers, ht0ord]
  have hcard_H : Nat.card ↥H = 2 := U9_center_card
  have hHz' : Subgroup.zpowers t0 = H :=
    Subgroup.eq_of_le_of_card_ge hzH (le_of_eq (by rw [hcard_H, hcard_t0]))
  have hHz : H = Subgroup.zpowers t0 := hHz'.symm
  have hmem : α t0 ∈ H := map_mem_H α hα ht0H
  rw [hHz] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hmod : t0 ^ (k % 2) = t0 ^ k := by
    have h := zpow_mod_orderOf t0 k
    rw [ht0ord] at h
    exact h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    have hαt0 : α t0 = 1 := by
      rw [← hk, ← hmod, h0, zpow_zero]
    have ht0eq : t0 = 1 := by
      apply α.injective
      rw [hαt0, map_one]
    have h1ord : orderOf t0 = 1 := by rw [ht0eq, orderOf_one]
    omega
  · rw [← hk, ← hmod, h1, zpow_one]

theorem conj_fixes_p0
    (α : MulAut ↥mclP) (hα : U9.map α.toMonoidHom = U9) :
    ∃ x : Equiv.Perm (Fin 275),
      (∀ g : ↥mclP, ((α g : ↥mclP) : Equiv.Perm (Fin 275)) = x * g * x⁻¹) ∧ x P0 = P0 := by
  obtain ⟨e, he, -⟩ := mcl_full_automorphism_model
  let x : Equiv.Perm (Fin 275) := ((e.symm α : mclR) : Equiv.Perm (Fin 275))
  have hconj : ∀ g : ↥mclP, ((α g : ↥mclP) : Equiv.Perm (Fin 275)) = x * g * x⁻¹ := by
    intro g
    have h := he (e.symm α) g
    simpa [x] using h
  refine ⟨x, hconj, ?_⟩
  have hfix : ∀ u ∈ U9, u.val (x⁻¹ P0) = x⁻¹ P0 := by
    intro u hu
    have hu' : α u ∈ U9 := by
      rw [← hα]
      exact Subgroup.mem_map_of_mem α.toMonoidHom hu
    have hfixu : (α u).val P0 = P0 := U9_fix (α u) hu'
    have hxux : (x * u.val * x⁻¹) P0 = P0 := by
      rw [← hconj u]
      exact hfixu
    have hxu : x (u.val (x⁻¹ P0)) = P0 := by
      simpa [Equiv.Perm.mul_apply] using hxux
    calc u.val (x⁻¹ P0)
        = x⁻¹ (x (u.val (x⁻¹ P0))) := by simp
      _ = x⁻¹ P0 := by rw [hxu]
  have hxinv : x⁻¹ P0 = P0 := (U9_fix_set (x⁻¹ P0)).mp hfix
  calc x P0 = x (x⁻¹ P0) := by rw [hxinv]
    _ = P0 := by simp

theorem map_P9
    (α : MulAut ↥mclP) (hα : U9.map α.toMonoidHom = U9) : P9.map α.toMonoidHom = P9 := by
  obtain ⟨x, hxconj, hxp0⟩ := conj_fixes_p0 α hα
  have hxinv : x⁻¹ P0 = P0 := by
    calc x⁻¹ P0 = x⁻¹ (x P0) := by rw [hxp0]
      _ = P0 := by simp
  have hle : P9.map α.toMonoidHom ≤ P9 := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_P9_iff] at hg ⊢
    constructor
    · have hgcent : g.val ∈ Subgroup.centralizer ({mclT0} : Set (Equiv.Perm (Fin 275))) :=
        (Subgroup.mem_inf.mp hg.1).2
      have hcomm_g : g.val * mclT0 = mclT0 * g.val :=
        (Subgroup.mem_centralizer_iff.mp hgcent mclT0 (by simp)).symm
      have ht0 : α (⟨mclT0, mclT0_facts.1⟩ : ↥mclP) = ⟨mclT0, mclT0_facts.1⟩ := map_t0 α hα
      have hconj_t0 : x * mclT0 * x⁻¹ = mclT0 := by
        have h := hxconj (⟨mclT0, mclT0_facts.1⟩ : ↥mclP)
        rw [ht0] at h
        exact h.symm
      refine Subgroup.mem_inf.mpr ⟨(α g).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : v = mclT0 := by simpa using hv
      rw [hv']
      change mclT0 * (α g).val = (α g).val * mclT0
      have hformula : (α g).val = x * g.val * x⁻¹ := hxconj g
      rw [hformula, ← hconj_t0]
      calc (x * mclT0 * x⁻¹) * (x * g.val * x⁻¹)
          = x * (mclT0 * g.val) * x⁻¹ := by group
        _ = x * (g.val * mclT0) * x⁻¹ := by rw [← hcomm_g]
        _ = (x * g.val * x⁻¹) * (x * mclT0 * x⁻¹) := by group
    · change (α g).val P0 = P0
      rw [hxconj g]
      calc (x * g.val * x⁻¹) P0
          = x (g.val (x⁻¹ P0)) := by simp [Equiv.Perm.mul_apply]
        _ = x (g.val P0) := by rw [hxinv]
        _ = x P0 := by rw [hg.2]
        _ = P0 := hxp0
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]

theorem package744101 :
    ∃ U P Q : Subgroup ↥CFSG.Sporadic.Schreier.mclP, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
      Nat.card P = 9 * Nat.card U ∧
      (∀ α : MulAut ↥CFSG.Sporadic.Schreier.mclP,
        U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
      Q ≤ P ∧ Nat.card Q = 9 ∧ ∀ q ∈ Q, q ^ 3 = 1 := by
  refine ⟨U9, P9, Q9, ?_, U9_le_P9, P9_card, fun α hα => map_P9 α hα, Q9_le_P9, Q9_card,
    Q9_pow_three⟩
  refine ⟨le_top, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 7) (by rw [U9_card]; norm_num)
  · have h_card : Nat.card U9 = 128 := U9_card
    have h_top : Nat.card (⊤ : Subgroup ↥mclP) = 898128000 := by
      rw [Subgroup.card_top, card_mclP]
    have h_mul : Nat.card U9 * (U9.subgroupOf ⊤).index = 898128000 := by
      have := Subgroup.card_mul_index (H := U9.subgroupOf ⊤)
      rw [h_top] at this
      simpa [card_subgroupOf_of_le (le_top : U9 ≤ ⊤)] using this
    have h_index : (U9.subgroupOf ⊤).index = 7016625 := by
      rw [h_card] at h_mul
      omega
    rw [h_index]
    norm_num

end CertificateChecks.KernelSpor.McLNine

end
