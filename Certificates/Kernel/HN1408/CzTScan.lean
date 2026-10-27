
module

public import Certificates.Kernel.HN1408.CzTFacts
public import Certificates.Kernel.HN1408.CzTCt

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzT

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HNRecog.HaradaModel

theorem class_z_card (hP : Nat.card ↥P1408 = 177408000) :
    (conjClass P1408 elemZ).ncard = 5775 := by
  have hm := ncard_conjClass_mul_card P1408 elemZ
  have hc : Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) = 30720 := by
    rw [← (czT_eq hP).1]
    exact (czT_eq hP).2
  change (conjClass P1408 elemZ).ncard *
    Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) = Nat.card ↥P1408 at hm
  rw [hc, hP] at hm
  omega

theorem card_cent_az (hP : Nat.card ↥P1408 = 177408000)
    (ha : ∀ g ∈ P1408, elemA * g = g * elemA) :
    Nat.card ↥(P1408 ⊓ centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408)))) = 30720 := by
  rw [cent_az ha, ← (czT_eq hP).1]
  exact (czT_eq hP).2

theorem class_az_card (hP : Nat.card ↥P1408 = 177408000)
    (ha : ∀ g ∈ P1408, elemA * g = g * elemA) :
    (conjClass P1408 (elemA * elemZ)).ncard = 5775 := by
  have hm := ncard_conjClass_mul_card P1408 (elemA * elemZ)
  change (conjClass P1408 (elemA * elemZ)).ncard *
    Nat.card ↥(P1408 ⊓ centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408)))) =
      Nat.card ↥P1408 at hm
  rw [card_cent_az hP ha, hP] at hm
  omega

theorem czScan_spec {T0 T1 : Nat → Nat} {F : Nat → Nat → Bool} (h : czScan T0 T1 F = true) :
    ∀ i < 1280, ∀ j < 24, F (T0 i) (T1 j) = true := by
  intro i hi j hj
  have h1 := allN_spec h i hi
  rw [strictB_app] at h1
  exact allN_spec h1 j hj

theorem ev_eq {i j x : Nat} (hi : i < 1280) (hj : j < 24) (hx : x < 1408) :
    pt (T0 i) (pt (T1 j) x) = ((t0P i * t1P j) ⟨x, hx⟩).val := by
  rw [← pt_pc (t0P_spec hi).2.1 hx]
  exact repC_pt (repC_pc (t0P_spec hi).2 (t1P_spec hj).2) hx

theorem scan_sound (hP : Nat.card ↥P1408 = 177408000) {F : Nat → Nat → Bool}
    {Q : Equiv.Perm (Fin 1408) → Prop} (h : czScan T0 T1 F = true)
    (hQ : ∀ i < 1280, ∀ j < 24, F (T0 i) (T1 j) = true → Q (t0P i * t1P j)) :
    ∀ g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))), Q g := by
  intro g hg
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hg
  exact hQ i hi j hj (czScan_spec h i hi j hj)

theorem commB_of {A B H : Nat} {g h : Equiv.Perm (Fin 1408)}
    (hev : ∀ x (hx : x < 1408), pt A (pt B x) = (g ⟨x, hx⟩).val) (hH : RepC H h)
    (hc : g * h = h * g) :
    commB A B H (pt A (pt B 0)) (pt A (pt B 1)) = true := by
  have e : ∀ x (hx : x < 1408), pt A (pt B (pt H x)) = pt H (pt A (pt B x)) := by
    intro x hx
    have hy : pt H x < 1408 := pt_lt hH.1 hx
    have hfx : (⟨pt H x, hy⟩ : Fin 1408) = h ⟨x, hx⟩ := Fin.ext (repC_pt hH hx)
    have hgx : pt A (pt B x) < 1408 := by rw [hev x hx]; exact Fin.isLt _
    have hfg : (⟨pt A (pt B x), hgx⟩ : Fin 1408) = g ⟨x, hx⟩ := Fin.ext (hev x hx)
    rw [hev _ hy, repC_pt hH hgx, hfx, hfg]
    have := congrArg (fun k : Equiv.Perm (Fin 1408) => (k ⟨x, hx⟩).val) hc
    simpa only [Equiv.Perm.mul_apply] using this
  unfold commB
  rw [e 0 (by norm_num), e 1 (by norm_num), Nat.beq_refl, Nat.beq_refl]

theorem isBase_of {g0 g1 v0 v1 : Nat} (h : isBase g0 g1 v0 v1 = true) : g0 = v0 ∧ g1 = v1 := by
  unfold isBase at h
  obtain ⟨a, b⟩ := mkA h
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b⟩

theorem base_eq (hP : Nat.card ↥P1408 = 177408000) {A B v0 v1 : Nat} {g v : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (hv : v ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (hev : ∀ x (hx : x < 1408), pt A (pt B x) = (g ⟨x, hx⟩).val)
    (hv0 : (v ⟨0, by norm_num⟩).val = v0) (hv1 : (v ⟨1, by norm_num⟩).val = v1)
    (h : isBase (pt A (pt B 0)) (pt A (pt B 1)) v0 v1 = true) : g = v := by
  obtain ⟨e0, e1⟩ := isBase_of h
  rw [hev 0 (by norm_num), ← hv0] at e0
  rw [hev 1 (by norm_num), ← hv1] at e1
  exact eq_of_base hP hg hv (Fin.ext e0) (Fin.ext e1)

theorem ctK_parts {T0 T1 : Nat → Nat} {H0 H1 H2 Ha Hz : Nat}
    (h : ctK T0 T1 H0 H1 H2 Ha Hz = true) :
    commP H0 Hz = true ∧ commP H1 Hz = true ∧ commP H2 Hz = true ∧ commP Ha Hz = true ∧
      czScan T0 T1 (ctRow H0 H1 H2 (pt Ha 0) (pt Ha 1) (pt Hz 0) (pt Hz 1) (pt (pc Ha Hz) 0)
        (pt (pc Ha Hz) 1)) = true := by
  unfold ctK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, f⟩ := mkA h
  exact ⟨a, b, c, d, f⟩

theorem ctRow_of {H0 H1 H2 a0 a1 z0 z1 c0 c1 A B : Nat}
    (h : ctRow H0 H1 H2 a0 a1 z0 z1 c0 c1 A B = true)
    (h0 : commB A B H0 (pt A (pt B 0)) (pt A (pt B 1)) = true)
    (h1 : commB A B H1 (pt A (pt B 0)) (pt A (pt B 1)) = true)
    (h2 : commB A B H2 (pt A (pt B 0)) (pt A (pt B 1)) = true) :
    isBase (pt A (pt B 0)) (pt A (pt B 1)) 0 1 = true ∨
      isBase (pt A (pt B 0)) (pt A (pt B 1)) a0 a1 = true ∨
      isBase (pt A (pt B 0)) (pt A (pt B 1)) z0 z1 = true ∨
      isBase (pt A (pt B 0)) (pt A (pt B 1)) c0 c1 = true := by
  unfold ctRow at h
  simp only [strictB_app] at h
  rcases mkIf h with ⟨-, h⟩ | ⟨hf, -⟩
  · rcases mkIf h with ⟨e, -⟩ | ⟨-, h⟩
    · exact Or.inl e
    rcases mkIf h with ⟨e, -⟩ | ⟨-, h⟩
    · exact Or.inr (Or.inl e)
    rcases mkIf h with ⟨e, -⟩ | ⟨-, h⟩
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr h))
  · rw [h0, h1, h2] at hf
    exact absurd hf (by decide)

theorem mem_cent_of {H : Nat} {h : Equiv.Perm (Fin 1408)} (hH : RepC H h) (hhP : h ∈ P1408)
    (hc : commP H (WK wordZ) = true) :
    h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  refine mem_inf.2 ⟨hhP, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hz : RepC (WK wordZ) elemZ := repC_word (by decide)
  have e := Nat.eq_of_beq_eq_true hc
  have h1 := repC_pc hH hz
  have h2 := repC_pc hz hH
  rw [e] at h1
  exact eq_of_repC h1 h2

theorem tGens_letters {l : Nat} (hl : l < 3) : lettersOK (tGens.getD l []) = true := by
  interval_cases l <;> decide

theorem cent_tGens (hP : Nat.card ↥P1408 = 177408000) {x : Equiv.Perm (Fin 1408)}
    (hx : x ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (hc : ∀ w ∈ tGens, x * elemW w = elemW w * x) :
    x = 1 ∨ x = elemA ∨ x = elemZ ∨ x = elemA * elemZ := by
  obtain ⟨c0, c1, c2, ca, hs⟩ := ctK_parts czT_ct
  have hz : RepC (WK wordZ) elemZ := repC_word (by decide)
  have ha : RepC (WK wordA) elemA := repC_word (by decide)
  have hac : RepC (pc (WK wordA) (WK wordZ)) (elemA * elemZ) := repC_pc ha hz
  have hzC : elemZ ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
    mem_inf.2 ⟨elemW_mem _, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have haC := mem_cent_of ha (elemW_mem _) ca
  have hacC := mul_mem haC hzC
  have hG : ∀ l < 3, RepC (WK (tGens.getD l [])) (elemW (tGens.getD l [])) :=
    fun l hl => repC_word (tGens_letters hl)
  have hcl : ∀ l < 3, x * elemW (tGens.getD l []) = elemW (tGens.getD l []) * x := by
    intro l hl
    refine hc _ ?_
    interval_cases l <;> decide
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hx
  have hev : ∀ y (hy : y < 1408), pt (T0 i) (pt (T1 j) y) = ((t0P i * t1P j) ⟨y, hy⟩).val :=
    fun y hy => ev_eq hi hj hy
  have hrow := czScan_spec hs i hi j hj
  rcases ctRow_of hrow (commB_of hev (hG 0 (by norm_num)) (hcl 0 (by norm_num)))
      (commB_of hev (hG 1 (by norm_num)) (hcl 1 (by norm_num)))
      (commB_of hev (hG 2 (by norm_num)) (hcl 2 (by norm_num))) with e | e | e | e
  · exact Or.inl (base_eq hP hx (one_mem _) hev rfl rfl e)
  · exact Or.inr (Or.inl (base_eq hP hx haC hev (repC_pt ha _).symm (repC_pt ha _).symm e))
  · exact Or.inr (Or.inr (Or.inl
      (base_eq hP hx hzC hev (repC_pt hz _).symm (repC_pt hz _).symm e)))
  · exact Or.inr (Or.inr (Or.inr
      (base_eq hP hx hacC hev (repC_pt hac _).symm (repC_pt hac _).symm e)))

end CFSG.KD.HN1408.CzT

end
