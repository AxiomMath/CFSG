module

public import CFSG.Certificates.Kernel.Sp62Pk.Sound
public import CFSG.Certificates.Kernel.Sp62W.Sound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS228Sp62.Data
public import Certificates.Kernel.KS228Sp62.ChecksT
public import Certificates.Kernel.KS228Sp62.ChecksO

public section

namespace CFSG.KD.Sp62

open CFSG.KC.Sp62 CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS228Sp62
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

theorem k12646_pk : canon6 k0C = true ∧ pk k0C = R12646 10 := by decide +kernel

theorem x12646_pk : canon6 x0C = true ∧ pk x0C = R12646 11 := by decide +kernel

theorem x12646sq_pk : canon6 (mul6 x0C x0C) = true ∧ pk (mul6 x0C x0C) = R12646 16 :=
  ⟨(mulE x12646_pk x12646_pk).1,
    (mulE x12646_pk x12646_pk).2.trans (Nat.eq_of_beq_eq_true (by decide +kernel))⟩

theorem elts12646_ok : eltsOK = true := by
  have hk := k12646_pk
  have hx := x12646_pk
  have p1 : genP.all pairCheck = true := all_pairs (by decide +kernel)
  have p2 : pairCheck k0P = true := pairCheck_of (by decide +kernel)
  have p3 : pairCheck x0P = true := pairCheck_of (by decide +kernel)
  have p4 : gkP.all pairCheck = true := all_pairs (by decide +kernel)
  have p5 : gxP.all pairCheck = true := all_pairs (by decide +kernel)
  have p6 : gnP.all pairCheck = true := all_pairs (by decide +kernel)
  have m5 := mulE hk (mulE hk (mulE hk (mulE hk hk)))
  have m3 := mulE hx (mulE hx hx)
  have e1 : (mul6 k0C (mul6 k0C (mul6 k0C (mul6 k0C k0C))) == one6) =
      Nat.beq (MULF (R12646 10) (MULF (R12646 10) (MULF (R12646 10) (MULF (R12646 10)
        (R12646 10))))) ONE := by
    rw [beq_pk m5.1 canon6_one6, m5.2, pk_one6]
  have e2 : (k0C == one6) = Nat.beq (R12646 10) ONE := by
    rw [beq_pk hk.1 canon6_one6, hk.2, pk_one6]
  have e3 : (mul6 x0C (mul6 x0C x0C) == one6) =
      Nat.beq (MULF (R12646 11) (MULF (R12646 11) (R12646 11))) ONE := by
    rw [beq_pk m3.1 canon6_one6, m3.2, pk_one6]
  have e4 : (x0C == one6) = Nat.beq (R12646 11) ONE := by
    rw [beq_pk hx.1 canon6_one6, hx.2, pk_one6]
  have e5 : commutes6 x0C k0C =
      Nat.beq (MULF (R12646 11) (R12646 10)) (MULF (R12646 10) (R12646 11)) := by
    unfold commutes6
    rw [beq_pk (mulE hx hk).1 (mulE hk hx).1, (mulE hx hk).2, (mulE hk hx).2]
  have c1 : gkP.all (fun p => commutes6 p.1 k0C) = true := all_comm hk (by decide +kernel)
  have c2 : gxP.all (fun p => commutes6 p.1 x0C) = true := all_comm hx (by decide +kernel)
  unfold eltsOK
  rw [p1, p2, p3, p4, p5, p6, e1, e2, e3, e4, e5, c1, c2]
  decide +kernel

theorem gps12646_ok : ∀ s < 2, ∃ x y, gpsH.getD s [] = x ++ y ∧
    (canon6 x = true ∧ pk x = at2 R12646 6 s) ∧ (canon6 y = true ∧ pk y = at2 R12646 8 s)
  | 0, _ => ⟨aC, aI, rfl, by decide +kernel, by decide +kernel⟩
  | 1, _ => ⟨bC, bI, rfl, by decide +kernel, by decide +kernel⟩
  | s + 2, h => absurd h (by omega)

theorem gk12646_ok : ∀ s < 2, canon6 ((gkP.map Prod.fst).getD s []) = true ∧
    pk ((gkP.map Prod.fst).getD s []) = at2 R12646 0 s := by decide +kernel

theorem gx12646_ok : ∀ s < 2, canon6 ((gxP.map Prod.fst).getD s []) = true ∧
    pk ((gxP.map Prod.fst).getD s []) = at2 R12646 2 s := by decide +kernel

theorem gn12646_ok : ∀ s < 2, canon6 ((gnP.map Prod.fst).getD s []) = true ∧
    pk ((gnP.map Prod.fst).getD s []) = at2 R12646 4 s := by decide +kernel

theorem clK12646 : closureOK (gkP.map Prod.fst) (tabK ()) 30 = true ∧
    ∀ t < 30, canon6 ((tabK ()).getD t []) = true ∧ pk ((tabK ()).getD t []) = recX R12646 17 t :=
  closure6_ok (gens := gkP.map Prod.fst) rfl (by decide) (by decide)
    gk12646_ok c12646tabK (by decide) (by decide) (by decide)

theorem clX12646 : closureOK (gxP.map Prod.fst) (tabX ()) 2160 = true ∧
    ∀ t < 2160, canon6 ((tabX ()).getD t []) = true ∧
      pk ((tabX ()).getD t []) = recX R12646 48 t :=
  closure6_ok (gens := gxP.map Prod.fst) rfl (by decide) (by decide)
    gx12646_ok c12646tabX (by decide) (by decide) (by decide)

theorem clN12646 : closureOK (gnP.map Prod.fst) (tabN ()) 60 = true ∧
    ∀ t < 60, canon6 ((tabN ()).getD t []) = true ∧
      pk ((tabN ()).getD t []) = recX R12646 2209 t :=
  closure6_ok (gens := gnP.map Prod.fst) rfl (by decide) (by decide)
    gn12646_ok c12646tabN (by decide) (by decide) (by decide)

theorem size_of_closureOK {gens : List (List ℕ)} {es : Array (List ℕ)} {n : ℕ}
    (h : closureOK gens es n = true) : es.size = n := by
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

theorem cube12646_eq {c : List ℕ} {C : ℕ} (hc : canon6 c = true ∧ pk c = C) :
    (!(mul6 c (mul6 c c) == one6) || c == one6 || c == x0C || c == mul6 x0C x0C) =
      cube12646F (R12646 11) (R12646 16) C := by
  have m := mulE hc (mulE hc hc)
  rw [beq_pk m.1 canon6_one6, m.2, pk_one6, beq_pk hc.1 canon6_one6, beq_pk hc.1 x12646_pk.1,
    beq_pk hc.1 x12646sq_pk.1, hc.2, pk_one6, x12646_pk.2, x12646sq_pk.2]
  rfl

theorem cube12646_ok : allCheck (fun c => !(mul6 c (mul6 c c) == one6) || c == one6 ||
    c == x0C || c == mul6 x0C x0C) (tabK ()) = true := by
  have hs := size_of_closureOK clK12646.1
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hs] at ht
  rw [cube12646_eq (clK12646.2 t ht)]
  exact CFSG.KC.G2Three.allBelow_g2 c12646cube (by decide) t ht

theorem kPows12646_pk : ∀ i < 4, canon6 (kPows.getD i []) = true ∧
    pk (kPows.getD i []) = R12646 (12 + i) := by
  intro i hi
  have hk := k12646_pk
  have m2 := mulE hk hk
  have m3 := mulE hk m2
  have m4 := mulE hk m3
  have h : ∀ i < 4, Nat.beq ([R12646 10, MULF (R12646 10) (R12646 10),
      MULF (R12646 10) (MULF (R12646 10) (R12646 10)),
      MULF (R12646 10) (MULF (R12646 10) (MULF (R12646 10) (R12646 10)))].getD i 0)
      (R12646 (12 + i)) = true := by decide +kernel
  have e := Nat.eq_of_beq_eq_true (h i hi)
  match i, hi with
  | 0, _ => exact ⟨hk.1, hk.2.trans e⟩
  | 1, _ => exact ⟨m2.1, m2.2.trans e⟩
  | 2, _ => exact ⟨m3.1, m3.2.trans e⟩
  | 3, _ => exact ⟨m4.1, m4.2.trans e⟩

theorem norm12646_eq {y : List ℕ} {Y : ℕ} (hy : canon6 y = true ∧ pk y = Y) :
    normK y = norm12646F (R12646 10) (R12646 12) (R12646 13) (R12646 14) (R12646 15) Y := by
  have hk := k12646_pk
  have q : ∀ i < 4, (mul6 y k0C == mul6 (kPows.getD i []) y) =
      Nat.beq (MULF Y (R12646 10)) (MULF (R12646 (12 + i)) Y) := by
    intro i hi
    have a := mulE hy hk
    have b := mulE (kPows12646_pk i hi) hy
    rw [beq_pk a.1 b.1, a.2, b.2]
  have q0 := q 0 (by decide)
  have q1 := q 1 (by decide)
  have q2 := q 2 (by decide)
  have q3 := q 3 (by decide)
  simp only [kPows, List.getD_cons_zero, List.getD_cons_succ] at q0 q1 q2 q3
  unfold normK
  rw [kPows]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [q0, q1, q2, q3]
  simp only [norm12646F, Bool.or_assoc]

theorem norm12646_ok :
    allCheck (fun y => !(normK y) || found (tabN ()) (indexMap (tabN ())) y) (tabX ()) = true := by
  have hs := size_of_closureOK clX12646.1
  have hn := size_of_closureOK clN12646.1
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hs] at ht
  have hy := clX12646.2 t ht
  have e := CFSG.KC.G2Three.allBelow_g2 c12646norm (by decide) t ht
  rw [norm12646_eq hy]
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
  rcases e with e | ⟨hw, ew⟩
  · rw [e]
    rfl
  · rw [Bool.or_eq_true]
    right
    rw [CFSG.KC.G2Three.found_indexMap]
    refine ⟨recF R12646 48 8 t, by rw [hn]; exact hw, ?_⟩
    have hz := clN12646.2 _ hw
    exact pk_inj hz.1 hy.1 (by rw [hz.2, hy.2, ew])

theorem o12646B_ok : ∀ j < 12, o12646B j = true
  | 0, _ => o12646B0 | 1, _ => o12646B1 | 2, _ => o12646B2 | 3, _ => o12646B3
  | 4, _ => o12646B4 | 5, _ => o12646B5 | 6, _ => o12646B6 | 7, _ => o12646B7
  | 8, _ => o12646B8 | 9, _ => o12646B9 | 10, _ => o12646B10 | 11, _ => o12646B11
  | j + 12, h => absurd h (by omega)

theorem o12646S_ok : ∀ j < 24, o12646S j = true
  | 0, _ => o12646S0 | 1, _ => o12646S1 | 2, _ => o12646S2 | 3, _ => o12646S3
  | 4, _ => o12646S4 | 5, _ => o12646S5 | 6, _ => o12646S6 | 7, _ => o12646S7
  | 8, _ => o12646S8 | 9, _ => o12646S9 | 10, _ => o12646S10 | 11, _ => o12646S11
  | 12, _ => o12646S12 | 13, _ => o12646S13 | 14, _ => o12646S14 | 15, _ => o12646S15
  | 16, _ => o12646S16 | 17, _ => o12646S17 | 18, _ => o12646S18 | 19, _ => o12646S19
  | 20, _ => o12646S20 | 21, _ => o12646S21 | 22, _ => o12646S22 | 23, _ => o12646S23
  | j + 24, h => absurd h (by omega)

theorem o12646T_ok : ∀ j < 12, o12646T j = true
  | 0, _ => o12646T0 | 1, _ => o12646T1 | 2, _ => o12646T2 | 3, _ => o12646T3
  | 4, _ => o12646T4 | 5, _ => o12646T5 | 6, _ => o12646T6 | 7, _ => o12646T7
  | 8, _ => o12646T8 | 9, _ => o12646T9 | 10, _ => o12646T10 | 11, _ => o12646T11
  | j + 12, h => absurd h (by omega)

theorem c12646orbK : (Nat.beq (recX R12646 2943 0) (R12646 10) &&
    tableK R12646 st12646 2943 48384 756 1512 756) = true := by
  have h0 := c12646orbK0
  simp only [Bool.and_eq_true] at h0
  obtain ⟨⟨hx, hc0⟩, hcn⟩ := h0
  have hS : stepG st12646 (recX R12646 2943) (recF R12646 2943 0) (recF R12646 2943 1)
      (recC R12646 2943) (recPOS R12646 2943) 48384 2 1512 = true := by
    unfold stepG
    simp only [Bool.and_eq_true]
    exact ⟨⟨hc0, hcn⟩, CFSG.KC.Sp62W.allBelow_of_sl (S := 24) (by decide) o12646S_ok⟩
  simp only [tableK, Bool.and_eq_true]
  exact ⟨hx, ⟨CFSG.KC.Sp62W.allBelow_of_sl (S := 12) (by decide) o12646B_ok, hS⟩,
    CFSG.KC.Sp62W.allBelow_of_sl (S := 12) (by decide) o12646T_ok⟩

theorem orbK12646 : orbitOK (orbitK ()) 48384 = true := by
  unfold orbitK
  exact orbit6_ok (GA := at2 R12646 6) (GB := at2 R12646 8) rfl (by decide) (by decide)
    gps12646_ok k12646_pk c12646orbK (by decide)
    (by decide) (by decide)

theorem orbX12646 : orbitOK (orbitX ()) 672 = true := by
  unfold orbitX
  exact orbit6_ok rfl (by decide) (by decide) gps12646_ok x12646_pk c12646orbX (by decide)
    (by decide) (by decide)

theorem sp62OK_ok : sp62OK () = true := by
  have h3 := clK12646.1
  have h4 := clX12646.1
  have h5 := clN12646.1
  have h7 := norm12646_ok
  unfold sp62OK tabsOK
  simp only [elts12646_ok, orbK12646, orbX12646, h3, h4, h5, cube12646_ok, h7, Bool.and_self]

end CFSG.KD.Sp62

end
