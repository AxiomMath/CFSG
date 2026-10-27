module

public import Certificates.Kernel.Sporadic.OddCore.S129061K0
public import Certificates.Kernel.Sporadic.OddCore.S129061K1
public import Certificates.Kernel.Sporadic.OddCore.S129061K2
public import Certificates.Kernel.Sporadic.OddCore.S129061K3
public import Certificates.Kernel.Sporadic.Suz.EndK
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndModel
public import CFSG.Certificates.Kernel.Spor.PSlpSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S129061

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.PSlp CFSG.KS.PSlp CFSG.Sporadic.SuzOddCore
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.RankTwoSporadic.Suz
  CertificateChecks.KernelSpor

theorem strictB_val (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem endK_spec {D : Nat} {R : List Nat} {a b : Nat} (h : endK D R a b = true) :
    nthD R a D = Suz2306.B0 ∧ nthD R b D = Suz2306.B1 := by
  cases R with
  | nil =>
    change false = true at h
    exact absurd h Bool.false_ne_true
  | cons x xs =>
    have h' : bAnd(Nat.beq (nthD (x :: xs) a D) Suz2306.B0,
        Nat.beq (nthD (x :: xs) b D) Suz2306.B1) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem prep_eq {P : Nat} {x y : Equiv.Perm (Fin 1782)} (hx : PRep 1782 11 P x)
    (hy : PRep 1782 11 P y) : x = y :=
  Equiv.ext fun p => Fin.ext ((hx p).symm.trans (hy p))

theorem prep_tP {i : Nat} (hi : i < 4) :
    PRep 1782 11 (SuzTP i) (suzInv i) := by
  have h := rep_suzInv hi
  rw [(OddCore.rep_facts hi).1] at h
  exact prep_of_rep h

theorem prep_B0 : PRep 1782 11 Suz2306.B0 suzB0 := by
  have h := rep_b0
  rw [Suz2306.b0Arr_eq] at h
  exact prep_of_rep h

theorem prep_B1 : PRep 1782 11 Suz2306.B1 suzB1 := by
  have h := rep_b1
  rw [Suz2306.b1Arr_eq] at h
  exact prep_of_rep h

theorem genK_sound {i : Nat}
    (hi : i < 4) {G GI H HI P c a b : Nat} (h : genK (SuzTP i) G GI H HI P c a b = true) :
    ∃ g ∈ suzM, ∃ h ∈ suzM,
      suzM ≤ Subgroup.closure {suzInv i, g * suzInv i * g⁻¹, h * suzInv i * h⁻¹} := by
  unfold genK at h
  obtain ⟨hG, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hH, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hsG, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hsH, h⟩ := (bAnd_iff _ _).1 h
  rw [strictB_val, strictB_val, strictB_val] at h
  obtain ⟨e0, e1⟩ := endK_spec h
  have pG := SuzEnd.prep_of hG
  have pH := SuzEnd.prep_of hH
  have pT := prep_tP hi
  set g := permOfArr 1782 (unpack 1782 11 G)
  set k := permOfArr 1782 (unpack 1782 11 H)
  set K := Subgroup.closure {suzInv i, g * suzInv i * g⁻¹, k * suzInv i * k⁻¹}
  let Good : Nat → Prop := fun X => ∃ x ∈ K, PRep 1782 11 X x
  have hT : Good (SuzTP i) := ⟨_, Subgroup.subset_closure (Set.mem_insert _ _), pT⟩
  have hmul : ∀ X Y, Good X → Good Y → Good (pcomp 1782 11 (mask 11) X Y) := by
    rintro X Y ⟨x, hx, px⟩ ⟨y, hy, py⟩
    exact ⟨x * y, K.mul_mem hx hy, prep_pcomp (by norm_num) px py⟩
  have hX : Good (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) G (SuzTP i)) GI) :=
    ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
      prep_pcomp (by norm_num) (prep_pcomp (by norm_num) pG.1 pT) pG.2⟩
  have hY : Good (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) H (SuzTP i)) HI) :=
    ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _))), prep_pcomp (by norm_num) (prep_pcomp (by norm_num) pH.1 pT) pH.2⟩
  have hR := slpGo_good (n := 1782) (w := 11) (fw := 12) (Good := Good) hT hmul c P
    (List.cons (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) H (SuzTP i)) HI)
      (List.cons (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) G (SuzTP i)) GI)
        (List.cons (SuzTP i) List.nil)))
    (by
      intro X hX'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX'
      rcases hX' with rfl | rfl | rfl
      · exact hY
      · exact hX
      · exact hT)
  obtain ⟨x0, hx0, px0⟩ := nthD_good hT hR a
  obtain ⟨x1, hx1, px1⟩ := nthD_good hT hR b
  rw [e0] at px0
  rw [e1] at px1
  refine ⟨g, mem_suzM_of (SuzEnd.inMA_of hG hsG), k, mem_suzM_of (SuzEnd.inMA_of hH hsH), ?_⟩
  rw [suzM, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [prep_eq prep_B0 px0]
    exact hx0
  · rw [prep_eq prep_B1 px1]
    exact hx1

theorem gen_facts :
    ∀ i < 4, ∃ g ∈ suzM, ∃ h ∈ suzM,
      suzM ≤ Subgroup.closure {suzInv i, g * suzInv i * g⁻¹, h * suzInv i * h⁻¹} := by
  intro i hi
  interval_cases i
  · exact genK_sound (i := 0) (by norm_num) class0
  · exact genK_sound (i := 1) (by norm_num) class1
  · exact genK_sound (i := 2) (by norm_num) class2
  · exact genK_sound (i := 3) (by norm_num) class3

end CertificateChecks.KernelSpor.S129061

end
