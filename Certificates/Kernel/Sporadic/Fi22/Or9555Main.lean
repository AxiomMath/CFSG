module

public import Certificates.Kernel.Sporadic.Fi22.Or9555Sound
public import Certificates.Kernel.Sporadic.Fi22.FivePinSound
public import CFSG.Certificates.Kernel.SetWalkPts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveSetOrbit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Or9555

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Raw CFSG.KC.SetWalk CertificateChecks.KernelSpor
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Certificates
open scoped Pointwise

theorem m12 : (4095 : Nat) = mask 12 := rfl

theorem m64 : (18446744073709551615 : Nat) = mask 64 := rfl

theorem rep_G {l : Int} {k : Nat} (hk : k < 2) (hl : l.toNat = k + 1) (hpos : 0 < l)
    {A : Equiv.Perm (Fin 3510)} (h : Rep 3510 (evalW [l]) A) :
    Rep 3510 (unpack 3510 12 (Fi22W.G k)) A := by
  intro x
  rw [← h x, evalW_cons, evalW_nil, compA_get x.2, idA_get x.2, ← Fi22W.orig_bind.2 k hk]
  simp only [letterA, hpos, if_true, hl, Nat.add_sub_cancel]

theorem s0_len : s0List.length = 360 := rfl

theorem s0_ok : pointListOK 3510 s0List = true := by decide +kernel

theorem ivl_disj (j j' : Fin 4) (h : j ≠ j') (i : ℕ)
    (a1 : (![0, 1, 1576, 23976] : Fin 4 → ℕ) j ≤ i)
    (a2 : i < (![1, 1576, 23976, 61776] : Fin 4 → ℕ) j)
    (b1 : (![0, 1, 1576, 23976] : Fin 4 → ℕ) j' ≤ i)
    (b2 : i < (![1, 1576, 23976, 61776] : Fin 4 → ℕ) j') : False := by
  fin_cases j <;> fin_cases j' <;> simp at h a1 a2 b1 b2 <;> omega

theorem orbit_pieces : ∀ G₁ G₂ : Equiv.Perm (Fin 3510), Rep 3510 g1A G₁ → Rep 3510 g2A G₂ →
    (G₁ • finSet 3510 s0List = finSet 3510 s0List ∧
      G₂ • finSet 3510 s0List = finSet 3510 s0List) ∧
    ∀ A B : Equiv.Perm (Fin 3510), Rep 3510 (evalW [1]) A → Rep 3510 (evalW [2]) B →
      ∃ E : Fin 4 → Set (Set (Fin 3510)), (∀ j, (E j).Finite) ∧
        (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        (∀ j, ∀ S ∈ E j, ∃ g ∈ Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))),
          S = g • ((![1, A, B, B * A] : Fin 4 → Equiv.Perm (Fin 3510)) j •
            finSet 3510 s0List)) ∧
        (∀ j, (E j).ncard = (![1, 1575, 22400, 37800] : Fin 4 → ℕ) j) := by
  intro G₁ G₂ h₁ h₂
  have r₁ : Rep 3510 (unpack 3510 12 (Fi22Pin.pin 6)) G₁ := by rw [← Fi22Pin.g1_eq]; exact h₁
  have r₂ : Rep 3510 (unpack 3510 12 (Fi22Pin.pin 7)) G₂ := by rw [← Fi22Pin.g2_eq]; exact h₂
  obtain ⟨hl0, hc1, hc2, hc3, hp0, hp1, hp2, hp3, hf1, hf2⟩ := roots
  rw [m12] at hl0 hc1 hc2 hc3 hf1 hf2
  have hpl := pointListOK_spec s0_ok
  obtain ⟨hv0, hS0⟩ := listK_pts (n := 3510) hl0 hpl.lt
    (hpl.sorted.imp fun {a b} hab => ne_of_lt hab)
  rw [s0_len] at hv0 hS0
  change pts 3510 12 360 (Or9555C 0) = finSet 3510 s0List at hS0
  refine ⟨⟨by rw [← hS0]; exact fixOK_pts hf1 r₁ hv0, by rw [← hS0]; exact fixOK_pts hf2 r₂ hv0⟩,
    fun A B hA hB => ?_⟩
  have rA := rep_G (l := 1) (k := 0) (by norm_num) rfl (by norm_num) hA
  have rB := rep_G (l := 2) (k := 1) (by norm_num) rfl (by norm_num) hB
  set T : Fin 4 → Set (Fin 3510) := fun j =>
    (![1, A, B, B * A] : Fin 4 → Equiv.Perm (Fin 3510)) j • finSet 3510 s0List with hT
  have hroot : ∀ j : Fin 4, Valid 3510 12 360 (Or9555C j) ∧ pts 3510 12 360 (Or9555C j) = T j := by
    intro j
    fin_cases j
    · exact ⟨hv0, by rw [hS0]; exact (one_smul _ _).symm⟩
    · change Valid 3510 12 360 (Or9555C 1) ∧ pts 3510 12 360 (Or9555C 1) = A • finSet 3510 s0List
      rw [hc1, ← hS0]
      exact pcomp_pts (by norm_num) rA hv0
    · change Valid 3510 12 360 (Or9555C 2) ∧ pts 3510 12 360 (Or9555C 2) = B • finSet 3510 s0List
      rw [hc2, ← hS0]
      exact pcomp_pts (by norm_num) rB hv0
    · change Valid 3510 12 360 (Or9555C 3) ∧
        pts 3510 12 360 (Or9555C 3) = (B * A) • finSet 3510 s0List
      obtain ⟨hv1, e1⟩ := pcomp_pts (by norm_num) rA hv0
      obtain ⟨hv3, e3⟩ := pcomp_pts (by norm_num) rB hv1
      rw [hc3, e3, e1, hS0, mul_smul]
      exact ⟨hv3, rfl⟩
  set lo : Fin 4 → ℕ := ![0, 1, 1576, 23976] with hlo
  set hi : Fin 4 → ℕ := ![1, 1576, 23976, 61776] with hhi
  have hP : ∀ j : Fin 4, Or9555P j % 2 ^ 20 = lo j ∧ Or9555P j / 2 ^ 20 = hi j := by
    intro j
    fin_cases j
    · change Or9555P 0 % 2 ^ 20 = 0 ∧ Or9555P 0 / 2 ^ 20 = 1
      rw [hp0]
      norm_num
    · change Or9555P 1 % 2 ^ 20 = 1 ∧ Or9555P 1 / 2 ^ 20 = 1576
      rw [hp1]
      norm_num
    · change Or9555P 2 % 2 ^ 20 = 1576 ∧ Or9555P 2 / 2 ^ 20 = 23976
      rw [hp2]
      norm_num
    · change Or9555P 3 % 2 ^ 20 = 23976 ∧ Or9555P 3 / 2 ^ 20 = 61776
      rw [hp3]
      norm_num
  have hhi61 : ∀ j : Fin 4, hi j ≤ 61776 := by
    intro j
    fin_cases j <;> simp [hhi]
  have hw := walk_sound (k := 360) (w := 12) (m := 4095) (wr := 64)
    (mr := 18446744073709551615) (R := Or9555R 0) (d := 9) (NC := 45) (G0 := Fi22Pin.pin 6)
    (G1 := Fi22Pin.pin 7) (N := 61776) (D := 128) (T := Or9555T) (CS := Or9555C)
    (CP := fun c => Or9555P c) chunks
  rw [m12, m64] at hw
  have hwp : ∀ j : Fin 4, ∀ i, lo j ≤ i → i < hi j → ∃ l : List Bool, keyR Or9555T i =
      keyS 360 12 (mask 12) 64 (mask 64) (Or9555R 0) 9
        (act 360 12 (mask 12) (Fi22Pin.pin 6) (Fi22Pin.pin 7) l (Or9555C j)) := by
    intro j i h1 h2
    obtain ⟨e1, e2⟩ := hP j
    exact hw j (by omega) i (by rw [e1]; exact h1) (by rw [e2]; exact h2)
  choose! L hL using hwp
  set f : Fin 4 → ℕ → Set (Fin 3510) := fun j i =>
    pts 3510 12 360 (act 360 12 (mask 12) (Fi22Pin.pin 6) (Fi22Pin.pin 7) (L j i) (Or9555C j))
    with hf
  have hact : ∀ j : Fin 4, ∀ i, Valid 3510 12 360
      (act 360 12 (mask 12) (Fi22Pin.pin 6) (Fi22Pin.pin 7) (L j i) (Or9555C j)) ∧
      ∃ g ∈ Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))), f j i = g • T j := by
    intro j i
    obtain ⟨hv, g, hg, e⟩ := act_pts (by norm_num) r₁ r₂ (hroot j).1 (L j i)
    exact ⟨hv, g, hg, by rw [← (hroot j).2]; exact e⟩
  have hinj : ∀ j j' : Fin 4, ∀ i i', lo j ≤ i → i < hi j → lo j' ≤ i' → i' < hi j' →
      f j i = f j' i' → i = i' := by
    intro j j' i i' a1 a2 b1 b2 e
    have hk := keyS_eq_of_pts (wr := 64) (R := Or9555R 0) (d := 9) (by norm_num)
      (hact j i).1 (hact j' i').1 e
    refine keys_inj i (by have := hhi61 j; omega) i' (by have := hhi61 j'; omega) ?_
    rw [hL j i a1 a2, hL j' i' b1 b2, hk]
  set E : Fin 4 → Set (Set (Fin 3510)) := fun j =>
    ((Finset.Ico (lo j) (hi j)).image (f j) : Set (Set (Fin 3510))) with hE
  refine ⟨E, fun j => Finset.finite_toSet _, fun j j' hjj => ?_, fun j S hS => ?_, fun j => ?_⟩
  · refine Set.disjoint_left.2 fun S hS hS' => ?_
    simp only [hE, Finset.coe_image, Finset.coe_Ico, Set.mem_image, Set.mem_Ico] at hS hS'
    obtain ⟨i, ⟨a1, a2⟩, rfl⟩ := hS
    obtain ⟨i', ⟨b1, b2⟩, e⟩ := hS'
    have := hinj j' j i' i b1 b2 a1 a2 e
    subst this
    exact ivl_disj j j' hjj i' a1 a2 b1 b2
  · simp only [hE, Finset.coe_image, Finset.coe_Ico, Set.mem_image, Set.mem_Ico] at hS
    obtain ⟨i, -, rfl⟩ := hS
    exact (hact j i).2
  · rw [hE, Set.ncard_coe_finset, Finset.card_image_of_injOn, Nat.card_Ico]
    · fin_cases j <;> rfl
    · intro i hi' i' hi'' e
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi' hi''
      exact hinj j j i i' hi'.1 hi'.2 hi''.1 hi''.2 e

end CertificateChecks.KernelSpor.Or9555

end
