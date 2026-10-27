module

public import CFSG.Certificates.Kernel.Sp6Two.Sound
public import Certificates.Kernel.Sp6Two.ChecksO
public import Certificates.Kernel.Sp6Two.ChecksC
public import Certificates.Kernel.Sp6Two.ChecksC0
public import Certificates.Kernel.Sp6Two.ChecksI
public import Certificates.Kernel.Sp6Two.ChecksT0

public section

namespace CFSG.KD.Sp6Two

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Sp6Two CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem pairs8151_ok : pairsOK = true := by
  unfold pairsOK
  rw [all_pairs (l := genP) (by decide +kernel), all_pairs (l := tP) (by decide +kernel),
    all_pairs (l := cent0P) (by decide +kernel), all_pairs (l := cent1P) (by decide +kernel),
    all_pairs (l := cent2P) (by decide +kernel), all_pairs (l := cent3P) (by decide +kernel),
    all_pairs (l := p0P) (by decide +kernel), all_pairs (l := p1P) (by decide +kernel),
    all_pairs (l := sylowP) (by decide +kernel)]
  rfl

theorem invs8151_ok : invsOK = true := by
  have h : tP.all (fun cc => canon6 cc.1 && Nat.beq (MULF (pk cc.1) (pk cc.1)) ONE &&
      !Nat.beq (pk cc.1) ONE) = true := by decide +kernel
  unfold invsOK
  rw [List.all_eq_true] at h ⊢
  intro cc hcc
  have e := h cc hcc
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨c, e1⟩, e2⟩ := e
  have m := mulE ⟨c, rfl⟩ ⟨c, rfl⟩
  rw [beq_pk m.1 canon6_one6, m.2, pk_one6, beq_pk c canon6_one6, pk_one6, e1, e2]
  rfl

theorem t8151_ok : (canon6 t0C = true ∧ pk t0C = REC 25) ∧ (canon6 t1C = true ∧ pk t1C = REC 26) ∧
    (canon6 t2C = true ∧ pk t2C = REC 27) ∧ (canon6 t3C = true ∧ pk t3C = REC 28) := by
  decide +kernel

theorem p8151_ok : (canon6 p0aC = true ∧ pk p0aC = REC 12) ∧
    (canon6 p0bC = true ∧ pk p0bC = REC 13) ∧ (canon6 p1aC = true ∧ pk p1aC = REC 14) ∧
    (canon6 p1bC = true ∧ pk p1bC = REC 15) := by
  decide +kernel

theorem comm8151_ok : commOK = true := by
  have h0 : (cent0P ++ p0P).all (fun cc => canon6 cc.1 &&
      Nat.beq (MULF (pk cc.1) (REC 25)) (MULF (REC 25) (pk cc.1))) = true := by decide +kernel
  have h1 : (cent1P ++ p1P).all (fun cc => canon6 cc.1 &&
      Nat.beq (MULF (pk cc.1) (REC 26)) (MULF (REC 26) (pk cc.1))) = true := by decide +kernel
  have h2 : cent2P.all (fun cc => canon6 cc.1 &&
      Nat.beq (MULF (pk cc.1) (REC 27)) (MULF (REC 27) (pk cc.1))) = true := by decide +kernel
  have h3 : cent3P.all (fun cc => canon6 cc.1 &&
      Nat.beq (MULF (pk cc.1) (REC 28)) (MULF (REC 28) (pk cc.1))) = true := by decide +kernel
  unfold commOK
  rw [all_comm t8151_ok.1 h0, all_comm t8151_ok.2.1 h1, all_comm t8151_ok.2.2.1 h2,
    all_comm t8151_ok.2.2.2 h3]
  rfl

theorem gps8151_ok : ∀ s < 2, ∃ x y, gpsH.getD s [] = x ++ y ∧
    (canon6 x = true ∧ pk x = at2 REC 21 s) ∧ (canon6 y = true ∧ pk y = at2 REC 23 s)
  | 0, _ => ⟨aC, aI, rfl, by decide +kernel, by decide +kernel⟩
  | 1, _ => ⟨bC, bI, rfl, by decide +kernel, by decide +kernel⟩
  | s + 2, h => absurd h (by omega)

theorem orb0_8151 : orbitOK orbit0 63 = true ∧ orbit0.size = 63 ∧
    ∀ t < 63, canon6 (orbit0.getD t []) = true ∧ pk (orbit0.getD t []) = recX REC 29 t :=
  orbit6_rec (fuel := 4000) rfl (by decide) (by decide) gps8151_ok t8151_ok.1 tabO0_ok
    (by decide) (by decide) (by decide)

theorem orb1_8151 : orbitOK orbit1 315 = true ∧ orbit1.size = 315 ∧
    ∀ t < 315, canon6 (orbit1.getD t []) = true ∧ pk (orbit1.getD t []) = recX REC 93 t :=
  orbit6_rec (fuel := 4000) rfl (by decide) (by decide) gps8151_ok t8151_ok.2.1 tabO1_ok
    (by decide) (by decide) (by decide)

theorem orb2_8151 : orbitOK orbit2 945 = true ∧ orbit2.size = 945 ∧
    ∀ t < 945, canon6 (orbit2.getD t []) = true ∧ pk (orbit2.getD t []) = recX REC 409 t :=
  orbit6_rec (fuel := 4000) rfl (by decide) (by decide) gps8151_ok t8151_ok.2.2.1 tabO2_ok
    (by decide) (by decide) (by decide)

theorem orb3_8151 : orbitOK orbit3 3780 = true ∧ orbit3.size = 3780 ∧
    ∀ t < 3780, canon6 (orbit3.getD t []) = true ∧ pk (orbit3.getD t []) = recX REC 1355 t :=
  orbit6_rec (fuel := 4000) rfl (by decide) (by decide) gps8151_ok t8151_ok.2.2.2 tabO3_ok
    (by decide) (by decide) (by decide)

theorem orbits8151_ok : orbitsOK = true := by
  unfold orbitsOK
  rw [orb0_8151.1, orb1_8151.1, orb2_8151.1, orb3_8151.1]
  rfl

theorem size_of_closureOK {gens : List (List ℕ)} {es : Array (List ℕ)} {n : ℕ}
    (h : closureOK gens es n = true) : es.size = n := by
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

theorem cent0_8151 : closureOK (cent0P.map Prod.fst) cent0 23040 = true ∧
    ∀ t < 23040, canon6 (cent0.getD t []) = true ∧ pk (cent0.getD t []) = recX REC 5136 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabC0_ok (by decide) (by decide)
    (by decide)

theorem cent1_8151 : closureOK (cent1P.map Prod.fst) cent1 4608 = true ∧
    ∀ t < 4608, canon6 (cent1.getD t []) = true ∧ pk (cent1.getD t []) = recX REC 28177 t :=
  closure6_ok rfl (by decide) (by decide) (by decide +kernel) tabC1_ok (by decide) (by decide)
    (by decide)

theorem cent2_8151 : closureOK (cent2P.map Prod.fst) cent2 1536 = true ∧
    ∀ t < 1536, canon6 (cent2.getD t []) = true ∧ pk (cent2.getD t []) = recX REC 32786 t :=
  closureKG_ok rfl (by decide) (by decide) (by decide) (by decide +kernel) tabC2_ok (by decide)
    (by decide) (by decide)

theorem cent3_8151 : closureOK (cent3P.map Prod.fst) cent3 384 = true ∧
    ∀ t < 384, canon6 (cent3.getD t []) = true ∧ pk (cent3.getD t []) = recX REC 34323 t :=
  closureKG_ok rfl (by decide) (by decide) (by decide) (by decide +kernel) tabC3_ok (by decide)
    (by decide) (by decide)

theorem cents8151_ok : centsOK = true := by
  unfold centsOK
  rw [cent0_8151.1, cent1_8151.1, cent2_8151.1, cent3_8151.1]
  rfl

theorem ps8151_ok : psOK = true := by
  unfold psOK
  rw [(closure6_ok (gens := p0P.map Prod.fst) rfl (by decide) (by decide) (by decide +kernel)
      tabP0_ok (by decide) (by decide) (by decide)).1,
    (closure6_ok (gens := p1P.map Prod.fst) rfl (by decide) (by decide) (by decide +kernel)
      tabP1_ok (by decide) (by decide) (by decide)).1]
  rfl

theorem sylow8151_ok : sylowOK = true := by
  have hS : closureOK (sylowP.map Prod.fst) sylowT 512 = true ∧
      ∀ t < 512, canon6 (sylowT.getD t []) = true ∧ pk (sylowT.getD t []) = recX REC 34728 t :=
    closureKG_ok rfl (by decide) (by decide) (by decide) (by decide +kernel) tabS_ok (by decide)
      (by decide) (by decide)
  unfold sylowOK
  rw [hS.1, invTest6 (size_of_closureOK hS.1) hS.2 orb0_8151.2.1 orb0_8151.2.2 orb1_8151.2.1
    orb1_8151.2.2 orb2_8151.2.1 orb2_8151.2.2 orb3_8151.2.1 orb3_8151.2.2 invS_ok (by decide)]
  rfl

theorem two8151_ok : twoOK = true := by
  unfold twoOK
  rw [centTest6 p8151_ok.1 p8151_ok.2.1 t8151_ok.1 (size_of_closureOK cent0_8151.1) cent0_8151.2
      two0_ok (by decide),
    centTest6 p8151_ok.2.2.1 p8151_ok.2.2.2 t8151_ok.2.1 (size_of_closureOK cent1_8151.1)
      cent1_8151.2 two1_ok (by decide)]
  rfl

theorem certAll8151_ok : certAll = true := by
  unfold certAll
  rw [pairs8151_ok, invs8151_ok, comm8151_ok, orbits8151_ok, cents8151_ok, ps8151_ok,
    sylow8151_ok, two8151_ok]
  rfl

end CFSG.KD.Sp6Two

end
