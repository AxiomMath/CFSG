module

public import CFSG.Certificates.Kernel.Sp6A2.Sound
public import Certificates.Kernel.Sp6A2.ChecksX
public import Certificates.Kernel.Sp6A2.ChecksS
public import Certificates.Kernel.Sp6A2.ChecksS3
public import Certificates.Kernel.Sp6A2.ChecksD
public import Certificates.Kernel.Sp6Two.Final
public import Certificates.Kernel.Sp62.Final

public section

namespace CFSG.KD.Sp6A2

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Sp6A2 CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.RankThree.PartTwo.Sec21.FF81.Am6 CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
  CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS
  CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

theorem c799751_Z7 : canon6 a2Z7 = true := by decide +kernel
theorem c799751_C0 : canon6 a2C0 = true := by decide +kernel
theorem c799751_S0 : canon6 a2S0 = true := by decide +kernel
theorem c799751_C1 : canon6 a2C1 = true := by decide +kernel
theorem c799751_S1 : canon6 a2S1 = true := by decide +kernel
theorem c799751_C2 : canon6 a2C2 = true := by decide +kernel
theorem c799751_S2 : canon6 a2S2 = true := by decide +kernel
theorem c799751_G0 : canon6 a2G0 = true := by decide +kernel
theorem c799751_G0I : canon6 a2G0I = true := by decide +kernel
theorem c799751_G1 : canon6 a2G1 = true := by decide +kernel
theorem c799751_G1I : canon6 a2G1I = true := by decide +kernel
theorem c799751_H : canon6 a2H = true := by decide +kernel
theorem c799751_HI : canon6 a2HI = true := by decide +kernel
theorem c799751_DA : canon6 a2DA = true := by decide +kernel
theorem c799751_DB : canon6 a2DB = true := by decide +kernel
theorem c799751_P : canon6 a2P = true := by decide +kernel
theorem c799751_Q : canon6 a2Q = true := by decide +kernel
theorem c799751_EP : canon6 a2EP = true := by decide +kernel
theorem c799751_EM : canon6 a2EM = true := by decide +kernel
theorem c799751_GY : canon6 a2GY = true := by decide +kernel
theorem c799751_GYI : canon6 a2GYI = true := by decide +kernel
theorem c799751_S01 : canon6 a2S01 = true := by decide +kernel
theorem c799751_S10 : canon6 a2S10 = true := by decide +kernel
theorem c799751_S12 : canon6 a2S12 = true := by decide +kernel
theorem c799751_S21 : canon6 a2S21 = true := by decide +kernel
theorem c799751_Sig : canon6 lsSig = true := by decide +kernel
theorem c799751_J : canon6 j6C = true := pk_j6C.1

theorem v799751 (a b c : ℕ) : canon6 (vecCode a b c) = true ∧
    pk (vecCode a b c) = VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) a b c :=
  vecCode_pk zc_ok a b c

theorem c799751_V : canon6 a2V = true := (v799751 1 2 0).1
theorem c799751_V2 : canon6 a2V2 = true := (v799751 2 1 0).1
theorem p799751_V : pk a2V = VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 1 2 0 :=
  (v799751 1 2 0).2
theorem p799751_V2 : pk a2V2 = VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 2 1 0 :=
  (v799751 2 1 0).2

macro "pk799751" : tactic => `(tactic| simp only [cj, commutes6, a2R, beq_pk, pk_mul6,
  canon6_mul6, canon6_one6, pk_one6, c799751_Z7, c799751_C0, c799751_S0, c799751_C1, c799751_S1,
  c799751_C2, c799751_S2, c799751_G0, c799751_G0I, c799751_G1, c799751_G1I, c799751_H, c799751_HI,
  c799751_DA, c799751_DB, c799751_P, c799751_Q, c799751_EP, c799751_EM, c799751_GY, c799751_GYI,
  c799751_S01, c799751_S10, c799751_S12, c799751_S21, c799751_Sig, c799751_J, c799751_V,
  c799751_V2, p799751_V, p799751_V2])

theorem x0_799751 : closureOK (a2XGens 0) (a2XTab 0) 168 = true ∧
    ∀ t < 168, canon6 ((a2XTab 0).getD t []) = true ∧
      pk ((a2XTab 0).getD t []) = recX REC 5126 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabX0_799751 (by decide) (by decide)
    (by decide)

theorem x1_799751 : closureOK (a2XGens 1) (a2XTab 1) 168 = true ∧
    ∀ t < 168, canon6 ((a2XTab 1).getD t []) = true ∧
      pk ((a2XTab 1).getD t []) = recX REC 5295 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabX1_799751 (by decide) (by decide)
    (by decide)

theorem x2_799751 : closureOK (a2XGens 2) (a2XTab 2) 168 = true ∧
    ∀ t < 168, canon6 ((a2XTab 2).getD t []) = true ∧
      pk ((a2XTab 2).getD t []) = recX REC 5464 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabX2_799751 (by decide) (by decide)
    (by decide)

theorem s0_799751 : closureOK [a2C0, a2S0] (closureT [a2C0, a2S0]) 6 = true ∧
    ∀ t < 6, canon6 ((closureT [a2C0, a2S0]).getD t []) = true ∧
      pk ((closureT [a2C0, a2S0]).getD t []) = recX REC 5633 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabS0_799751 (by decide) (by decide)
    (by decide)

theorem s1_799751 : closureOK [a2C1, a2S1] (closureT [a2C1, a2S1]) 6 = true ∧
    ∀ t < 6, canon6 ((closureT [a2C1, a2S1]).getD t []) = true ∧
      pk ((closureT [a2C1, a2S1]).getD t []) = recX REC 5640 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabS1_799751 (by decide) (by decide)
    (by decide)

theorem s2_799751 : closureOK [a2C2, a2S2] (closureT [a2C2, a2S2]) 6 = true ∧
    ∀ t < 6, canon6 ((closureT [a2C2, a2S2]).getD t []) = true ∧
      pk ((closureT [a2C2, a2S2]).getD t []) = recX REC 5647 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabS2_799751 (by decide) (by decide)
    (by decide)

theorem k4_799751 : closureOK a2K4Gens (closureT a2K4Gens) 6 = true ∧
    ∀ t < 6, canon6 ((closureT a2K4Gens).getD t []) = true ∧
      pk ((closureT a2K4Gens).getD t []) = recX REC 5654 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabK4_799751 (by decide) (by decide)
    (by decide)

theorem k2_799751 : closureOK a2K2Gens (closureT a2K2Gens) 6 = true ∧
    ∀ t < 6, canon6 ((closureT a2K2Gens).getD t []) = true ∧
      pk ((closureT a2K2Gens).getD t []) = recX REC 5661 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabK2_799751 (by decide) (by decide)
    (by decide)

theorem d_799751 : closureOK a2DGens (closureT a2DGens) 36 = true ∧
    ∀ t < 36, canon6 ((closureT a2DGens).getD t []) = true ∧
      pk ((closureT a2DGens).getD t []) = recX REC 5668 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabD_799751 (by decide) (by decide)
    (by decide)

theorem c7_799751 : closureOK (c7P.map Prod.fst) (closureT (c7P.map Prod.fst)) 648 = true ∧
    ∀ t < 648, canon6 ((closureT (c7P.map Prod.fst)).getD t []) = true ∧
      pk ((closureT (c7P.map Prod.fst)).getD t []) = recX REC 5705 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabC7_799751 (by decide) (by decide)
    (by decide)

theorem cz3_799751 : (closureT ((centGens 3).map Prod.fst)).size = 108 ∧
    ∀ t < 108, canon6 ((closureT ((centGens 3).map Prod.fst)).getD t []) = true ∧
      pk ((closureT ((centGens 3).map Prod.fst)).getD t []) = recX CFSG.KD.Sp62.REC 6521 t :=
  ⟨CFSG.KD.Sp6Two.size_of_closureOK (clos_ok 3).1, (clos_ok 3).2⟩

theorem cz2_799751 : (closureT ((centGens 2).map Prod.fst)).size = 2160 ∧
    ∀ t < 2160, canon6 ((closureT ((centGens 2).map Prod.fst)).getD t []) = true ∧
      pk ((closureT ((centGens 2).map Prod.fst)).getD t []) = recX CFSG.KD.Sp62.REC 4360 t :=
  ⟨CFSG.KD.Sp6Two.size_of_closureOK (clos_ok 2).1, (clos_ok 2).2⟩

theorem cz4_799751 : (closureT ((centGens 4).map Prod.fst)).size = 108 ∧
    ∀ t < 108, canon6 ((closureT ((centGens 4).map Prod.fst)).getD t []) = true ∧
      pk ((closureT ((centGens 4).map Prod.fst)).getD t []) = recX CFSG.KD.Sp62.REC 6630 t :=
  ⟨CFSG.KD.Sp6Two.size_of_closureOK (clos_ok 4).1, (clos_ok 4).2⟩

theorem x_799751 : xCheck = true := by
  unfold xCheck
  rw [finRange_three]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [x0_799751.1, x1_799751.1, x2_799751.1,
    pairCheck_of (by decide +kernel : pairT (a2Z7, a2Z7I) = true),
    pairCheck_of (by decide +kernel : pairT (a2Tau0, a2Tau0) = true),
    pairCheck_of (by decide +kernel : pairT (a2Tau1, a2Tau1) = true),
    pairCheck_of (by decide +kernel : pairT (a2Tau2, a2Tau2) = true)]
  rfl

theorem scan_799751 : scanCheck = true := by
  have hz : canon6 a2Z7 = true ∧ pk a2Z7 = 17324581188 := ⟨c799751_Z7, by decide +kernel⟩
  have ho : REC 20 = 5126 ∧ REC (20 + 1) = 5295 ∧ REC (20 + 2) = 5464 := by decide +kernel
  have h0 := And.intro (CFSG.KD.Sp6Two.size_of_closureOK x0_799751.1) x0_799751.2
  have h1 := And.intro (CFSG.KD.Sp6Two.size_of_closureOK x1_799751.1) x1_799751.2
  have h2 := And.intro (CFSG.KD.Sp6Two.size_of_closureOK x2_799751.1) x2_799751.2
  unfold scanCheck
  dsimp only
  rw [scan_orbit hz CFSG.KD.Sp6Two.orb0_8151.2.1 CFSG.KD.Sp6Two.orb0_8151.2.2 h0 h1 h2 ho
      (fun t ht => scanK_at scanO0_799751 (by decide) t (by omega) (by omega)),
    scan_orbit hz CFSG.KD.Sp6Two.orb1_8151.2.1 CFSG.KD.Sp6Two.orb1_8151.2.2 h0 h1 h2 ho
      (fun t ht => scanK_at scanO1_799751 (by decide) t (by omega) (by omega)),
    scan_orbit hz CFSG.KD.Sp6Two.orb2_8151.2.1 CFSG.KD.Sp6Two.orb2_8151.2.2 h0 h1 h2 ho
      (fun t ht => by
        by_cases a : t < 512
        · exact scanK_at scanO2a_799751 (by decide) t (by omega) (by omega)
        · exact scanK_at scanO2b_799751 (by decide) t (by omega) (by omega)),
    scan_orbit hz CFSG.KD.Sp6Two.orb3_8151.2.1 CFSG.KD.Sp6Two.orb3_8151.2.2 h0 h1 h2 ho
      (fun t ht => by
        by_cases a : t < 512
        · exact scanK_at scanO3a_799751 (by decide) t (by omega) (by omega)
        by_cases b : t < 1024
        · exact scanK_at scanO3b_799751 (by decide) t (by omega) (by omega)
        by_cases c : t < 1536
        · exact scanK_at scanO3c_799751 (by decide) t (by omega) (by omega)
        by_cases d : t < 2048
        · exact scanK_at scanO3d_799751 (by decide) t (by omega) (by omega)
        by_cases e : t < 2560
        · exact scanK_at scanO3e_799751 (by decide) t (by omega) (by omega)
        by_cases f : t < 3072
        · exact scanK_at scanO3f_799751 (by decide) t (by omega) (by omega)
        by_cases g : t < 3584
        · exact scanK_at scanO3g_799751 (by decide) t (by omega) (by omega)
        · exact scanK_at scanO3h_799751 (by decide) t (by omega) (by omega))]
  rfl

theorem bad_799751 : badCheck = true := by
  have hX0 := CFSG.KD.Sp6Two.size_of_closureOK x0_799751.1
  have hX1 := CFSG.KD.Sp6Two.size_of_closureOK x1_799751.1
  unfold badCheck badOne
  rw [pairCheck_of (by decide +kernel : pairT (a2C0, a2C0I) = true),
    pairCheck_of (by decide +kernel : pairT (a2S0, a2S0) = true),
    pairCheck_of (by decide +kernel : pairT (a2G0, a2G0I) = true),
    pairCheck_of (by decide +kernel : pairT (a2C1, a2C1I) = true),
    pairCheck_of (by decide +kernel : pairT (a2S1, a2S1) = true),
    pairCheck_of (by decide +kernel : pairT (a2G1, a2G1I) = true),
    found_of_inK hX0 x0_799751.2 ⟨c799751_C0, rfl⟩ (by decide +kernel),
    found_of_inK hX0 x0_799751.2 ⟨c799751_S0, rfl⟩ (by decide +kernel),
    found_of_inK hX1 x1_799751.2 ⟨c799751_C1, rfl⟩ (by decide +kernel),
    found_of_inK hX1 x1_799751.2 ⟨c799751_S1, rfl⟩ (by decide +kernel),
    s0_799751.1, s1_799751.1]
  unfold cj
  rw [countP_comm (hi := 2) cz4_799751.1 cz4_799751.2
      (mulE (mulE ⟨c799751_G0, rfl⟩ ⟨c799751_S0, rfl⟩) ⟨c799751_G0I, rfl⟩) (by decide),
    countP_comm (hi := 2) cz4_799751.1 cz4_799751.2
      (mulE (mulE ⟨c799751_G1, rfl⟩ ⟨c799751_S1, rfl⟩) ⟨c799751_G1I, rfl⟩) (by decide)]
  pk799751
  decide +kernel

theorem good_799751 : goodCheck = true := by
  have hX2 := CFSG.KD.Sp6Two.size_of_closureOK x2_799751.1
  have hK4 := CFSG.KD.Sp6Two.size_of_closureOK k4_799751.1
  unfold goodCheck
  rw [pairCheck_of (by decide +kernel : pairT (a2C2, a2C2I) = true),
    pairCheck_of (by decide +kernel : pairT (a2S2, a2S2) = true),
    pairCheck_of (by decide +kernel : pairT (a2H, a2HI) = true),
    found_of_inK hX2 x2_799751.2 ⟨c799751_C2, rfl⟩ (by decide +kernel),
    found_of_inK hX2 x2_799751.2 ⟨c799751_S2, rfl⟩ (by decide +kernel),
    s2_799751.1, k4_799751.1]
  unfold cj
  rw [found_of_inK hK4 k4_799751.2
    (mulE (mulE ⟨c799751_H, rfl⟩ ⟨c799751_S2, rfl⟩) ⟨c799751_HI, rfl⟩) (by decide +kernel)]
  pk799751
  decide +kernel

theorem dGroup_799751 : dGroup = true := by
  unfold dGroup
  rw [d_799751.1, pairCheck_of (by decide +kernel : pairT (a2DA, a2DAI) = true),
    pairCheck_of (by decide +kernel : pairT (a2DB, a2DB) = true)]
  pk799751
  decide +kernel

theorem vecs_799751 :
    (canon6 (vecCode 1 1 0) = true ∧ pk (vecCode 1 1 0) = REC 17715) ∧
    (canon6 (vecCode 2 2 0) = true ∧ pk (vecCode 2 2 0) = REC (Nat.add 17715 1)) ∧
    (canon6 (vecCode 0 0 1) = true ∧ pk (vecCode 0 0 1) = REC (Nat.add 17715 2)) ∧
    (canon6 (vecCode 0 0 2) = true ∧ pk (vecCode 0 0 2) = REC (Nat.add 17715 3)) ∧
    (canon6 (vecCode 1 1 1) = true ∧ pk (vecCode 1 1 1) = REC (Nat.add 17715 4)) ∧
    (canon6 (vecCode 2 2 2) = true ∧ pk (vecCode 2 2 2) = REC (Nat.add 17715 5)) ∧
    (canon6 (vecCode 1 1 2) = true ∧ pk (vecCode 1 1 2) = REC (Nat.add 17715 6)) ∧
    (canon6 (vecCode 2 2 1) = true ∧ pk (vecCode 2 2 1) = REC (Nat.add 17715 7)) ∧
    (canon6 fl2C = true ∧ pk fl2C = REC (Nat.add 17715 8)) := by
  refine ⟨⟨(v799751 1 1 0).1, ?_⟩, ⟨(v799751 2 2 0).1, ?_⟩, ⟨(v799751 0 0 1).1, ?_⟩,
    ⟨(v799751 0 0 2).1, ?_⟩, ⟨(v799751 1 1 1).1, ?_⟩, ⟨(v799751 2 2 2).1, ?_⟩,
    ⟨(v799751 1 1 2).1, ?_⟩, ⟨(v799751 2 2 1).1, ?_⟩, by decide +kernel⟩ <;>
  · rw [(v799751 _ _ _).2]
    decide +kernel

theorem listed_799751 {a : List ℕ} {A : ℕ} (ha : canon6 a = true ∧ pk a = A) :
    cenListed a = listedF REC 17715 A := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, -⟩ := vecs_799751
  unfold cenListed listedF
  rw [beq_pk ha.1 v0.1, beq_pk ha.1 v1.1, beq_pk ha.1 v2.1, beq_pk ha.1 v3.1, beq_pk ha.1 v4.1,
    beq_pk ha.1 v5.1, beq_pk ha.1 v6.1, beq_pk ha.1 v7.1, v0.2, v1.2, v2.2, v3.2, v4.2, v5.2,
    v6.2, v7.2, ha.2]

theorem cen_799751 {a t : List ℕ} {A T : ℕ} (ha : canon6 a = true ∧ pk a = A)
    (ht : canon6 t = true ∧ pk t = T) :
    cenCount a t = cenK CFSG.KD.Sp62.REC REC 17715 A T := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := vecs_799751
  unfold cenCount cenK cj
  rw [beq_pk ha.1 v0.1, beq_pk ha.1 v1.1, beq_pk ha.1 v2.1, beq_pk ha.1 v3.1, beq_pk ha.1 v4.1,
    beq_pk ha.1 v5.1, beq_pk ha.1 v6.1, beq_pk ha.1 v7.1, v0.2, v1.2, v2.2, v3.2, v4.2, v5.2,
    v6.2, v7.2, ha.2,
    countP_comm (hi := 2) cz3_799751.1 cz3_799751.2 ht (by decide),
    countP_comm (hi := 34) cz2_799751.1 cz2_799751.2 ht (by decide),
    countP_comm (hi := 11) (CFSG.KD.Sp6Two.size_of_closureOK c7_799751.1) c7_799751.2 ht
      (by decide),
    countP_comm (hi := 11) (CFSG.KD.Sp6Two.size_of_closureOK c7_799751.1) c7_799751.2
      (mulE (mulE v8 ht) v8)
      (by decide)]
  simp only [nIf_eq']

theorem dPair_799751 {a t : List ℕ} {A T : ℕ} (ha : canon6 a = true ∧ pk a = A)
    (ht : canon6 t = true ∧ pk t = T) (h : dF CFSG.KD.Sp62.REC REC 17715 5661 A T = true) :
    dPair (indexMap (closureT a2K2Gens)) a t = true := by
  have hK := CFSG.KD.Sp6Two.size_of_closureOK k2_799751.1
  have m1 := mulE ha ha
  have m2 := mulE m1 ha
  have m3 := mulE ht ht
  have m4 := mulE (mulE ht ha) ht
  have hf : (mul6 (mul6 a a) a == one6 && !(a == one6) && mul6 t t == one6 && !(t == one6) &&
      mul6 (mul6 t a) t == mul6 a a) = dFilt A T := by
    rw [beq_pk m2.1 canon6_one6, beq_pk ha.1 canon6_one6, beq_pk m3.1 canon6_one6,
      beq_pk ht.1 canon6_one6, beq_pk m4.1 m1.1, m2.2, m3.2, m4.2, m1.2, ha.2, ht.2, pk_one6]
    rfl
  unfold dF at h
  unfold dPair
  rw [hf]
  cases hq : dFilt A T
  · rfl
  · rw [hq] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [found_of_inK hK k2_799751.2 ha h1, found_of_inK hK k2_799751.2 ht h2]
      simp
    · have hne : cenK CFSG.KD.Sp62.REC REC 17715 A T ≠ 36 := by
        intro e
        rw [e] at h2
        exact absurd h2 (by decide)
      rw [listed_799751 ha, cen_799751 ha ht, h1]
      simp [hne]

theorem dClass_799751 : dClass = true := by
  have hD := CFSG.KD.Sp6Two.size_of_closureOK d_799751.1
  have rows : ∀ i < 36, ∀ j < 36,
      dF CFSG.KD.Sp62.REC REC 17715 5661 (recX REC 5668 i) (recX REC 5668 j) = true := by
    intro i hi j hj
    have e : ∀ k < 6, ∀ r < 6, Nat.add (Nat.mul 6 k) r = i →
        dRows CFSG.KD.Sp62.REC REC 17715 5661 5668 (Nat.mul 6 k) 6 = true →
        dF CFSG.KD.Sp62.REC REC 17715 5661 (recX REC 5668 i) (recX REC 5668 j) = true := by
      intro k _ r hr hkr hk
      have := dRows_at hk (by decide) r hr j hj
      rwa [hkr] at this
    have hr : Nat.add (Nat.mul 6 (i / 6)) (i % 6) = i := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rcases (by omega : i / 6 = 0 ∨ i / 6 = 1 ∨ i / 6 = 2 ∨ i / 6 = 3 ∨ i / 6 = 4 ∨ i / 6 = 5) with
      q | q | q | q | q | q <;> rw [q] at hr
    · exact e 0 (by decide) _ (Nat.mod_lt _ (by decide)) hr ch799751d.i0
    · exact e 1 (by decide) _ (Nat.mod_lt _ (by decide)) hr ch799751d.i1
    · exact e 2 (by decide) _ (Nat.mod_lt _ (by decide)) hr ch799751d.i2
    · exact e 3 (by decide) _ (Nat.mod_lt _ (by decide)) hr ch799751d.i3
    · exact e 4 (by decide) _ (Nat.mod_lt _ (by decide)) hr ch799751d.i4
    · exact e 5 (by decide) _ (Nat.mod_lt _ (by decide)) hr ch799751d.i5
  unfold dClass
  refine CFSG.KC.G2Three.allCheck_of fun i hi => CFSG.KC.G2Three.allCheck_of fun j hj => ?_
  rw [hD] at hi hj
  exact dPair_799751 (d_799751.2 i hi) (d_799751.2 j hj) (rows i hi j hj)

theorem dCheck_799751 : dCheck = true := by
  unfold dCheck
  rw [dGroup_799751, dClass_799751]
  rfl

theorem chain_799751 : chainCheck = true := by
  have hX2 := CFSG.KD.Sp6Two.size_of_closureOK x2_799751.1
  have hK := CFSG.KD.Sp6Two.size_of_closureOK k2_799751.1
  have hall : ∀ t < 6, (!(Nat.beq (MULF (recX REC 5661 t) (recX REC 5661 t)) ONE) ||
      Nat.beq (recX REC 5661 t) ONE || Nat.beq (recX REC 5661 t) (pk a2P) ||
      Nat.beq (recX REC 5661 t) (pk a2Q) ||
      Nat.beq (recX REC 5661 t) (MULF (MULF (pk a2P) (pk a2Q)) (pk a2P))) = true := by
    decide +kernel
  unfold chainCheck chainPairs chainXstar chainK2 chainSiegel chainWords
  rw [pairCheck_of (by decide +kernel : pairT (a2GY, a2GYI) = true),
    pairCheck_of (by decide +kernel : pairT (a2P, a2P) = true),
    pairCheck_of (by decide +kernel : pairT (a2Q, a2Q) = true),
    pairCheck_of (by decide +kernel : pairT (a2EP, a2EP) = true),
    pairCheck_of (by decide +kernel : pairT (a2EM, a2EM) = true), k2_799751.1,
    CFSG.KC.G2Three.allCheck_of (es := closureT a2K2Gens) fun t ht => by
      rw [hK] at ht
      have x := k2_799751.2 t ht
      have := hall t ht
      generalize (closureT a2K2Gens).getD t [] = y at x ⊢
      obtain ⟨cy, py⟩ := x
      simp only [a2R, beq_pk, pk_mul6, canon6_mul6, canon6_one6, pk_one6, cy, c799751_P,
        c799751_Q]
      rw [py]
      exact this]
  unfold cj
  rw [found_of_inK hX2 x2_799751.2
      (mulE (mulE ⟨c799751_HI, rfl⟩ ⟨c799751_EP, rfl⟩) ⟨c799751_H, rfl⟩) (by decide +kernel),
    found_of_inK hX2 x2_799751.2
      (mulE (mulE ⟨c799751_HI, rfl⟩ ⟨c799751_EM, rfl⟩) ⟨c799751_H, rfl⟩) (by decide +kernel)]
  pk799751
  decide +kernel

theorem a2_ok : a2Check = true := by
  unfold a2Check
  rw [x_799751, scan_799751, bad_799751, good_799751, dCheck_799751, chain_799751]
  rfl

end CFSG.KD.Sp6A2

end
