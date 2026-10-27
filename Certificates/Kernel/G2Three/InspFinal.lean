module

public import Certificates.Kernel.G2Three.InspChecks
public import Certificates.Kernel.G2Three.S7Final

public section

namespace CFSG.KD.G2Three

open CFSG.KC.G2Three CFSG.RankThree.PartTwo.Census.Carrier.G2Three Certificates.S5RowsG23
  Certificates.S7G23Insp CFSG.Quasithin.G2U

theorem insp_es {i : ℕ} (hi : i < 64) : canon14 (es i) = true ∧ pk (es i) = XS i :=
  tabS.2.2.2.2 i hi

theorem insp_k1s : ∀ a ∈ k1s, a < 64 := by decide

theorem insp_k2s : ∀ a ∈ k2s, a < 64 := by decide

theorem insp_beq_comm (a b : ℕ) : Nat.beq a b = Nat.beq b a :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, Nat.beq_eq]; exact eq_comm)

theorem insp_closedL {ks : List ℕ} (hks : ∀ a ∈ ks, a < 64) : closedL ks = closedK XS ks := by
  unfold closedL closedK
  refine all_congr' fun a ha => all_congr' fun b hb => any_congr' fun c hc => ?_
  have e := mulE consts_ok (insp_es (hks a ha)) (insp_es (hks b hb))
  rw [beq_pk e.1 (insp_es (hks c hc)).1, e.2, (insp_es (hks c hc)).2]

theorem insp_sq {i : ℕ} (hi : i < 64) :
    (sq14 (es i) == tc) = Nat.beq (MUL (XS i) (XS i)) (XO 0) := by
  have e := mulE consts_ok (insp_es hi) (insp_es hi)
  rw [sq14, beq_pk e.1 btc.1, e.2, btc.2]

theorem insp_contains {c : List ℕ} (hc : canon14 c = true) :
    elemsX.contains c = memK (pk c) ((List.range 576).map XX) := by
  rw [← tX.2, ← Array.contains_toList, List.contains_eq_any_beq]
  unfold memK
  rw [List.any_map]
  refine any_congr' fun y hy => ?_
  rw [Function.comp_apply, beq_pk hc (tX.1 y hy), insp_beq_comm]

theorem insp_foldl {f : List ℕ → List ℕ → List ℕ} {F : ℕ → ℕ → ℕ}
    (hf : ∀ a w, canon14 a = true → canon14 w = true →
      canon14 (f a w) = true ∧ pk (f a w) = F (pk a) (pk w)) :
    ∀ (L : List (List ℕ)) (acc : List ℕ), (∀ c ∈ L, canon14 c = true) → canon14 acc = true →
      canon14 (L.foldl f acc) = true ∧ pk (L.foldl f acc) = (L.map pk).foldl F (pk acc)
  | [], _, _, h => ⟨h, rfl⟩
  | c :: L, acc, hL, h => by
    have e := hf acc c h (hL c (by simp))
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ← e.2]
    exact insp_foldl hf L _ (fun c' hc' => hL c' (by simp [hc'])) e.1

theorem insp_word : (∀ c ∈ wordG (), canon14 c = true) ∧ (wordG ()).map pk = inspLetters GA := by
  refine ⟨fun c hc => ?_, ?_⟩
  · simp only [wordG, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bx0.1
    · exact bx1.1
    · exact bx0.1
    · exact by0.1
    · exact sy1.1
    · exact by0.1
    · exact by1.1
    · exact bx1.1
    · exact sx0.1
    · exact by0.1
  · simp only [wordG, inspLetters, List.map_cons, List.map_nil, bx0.2, bx1.2, by0.2, by1.2, sx0.2,
      sy1.2]

theorem insp_g : canon14 (gc ()) = true ∧ pk (gc ()) = inspWord GA := by
  have h := insp_foldl (f := mul14) (F := MUL) (fun a w ha hw => ⟨canon14_mul14 a w, pkm ha hw⟩)
    (wordG ()) one14 insp_word.1 canon14_one14
  rw [insp_word.2, bone] at h
  exact h

theorem insp_gi : canon14 (gic ()) = true ∧ pk (gic ()) = inspWordInv GA := by
  have h := insp_foldl (f := fun a w => mul14 a (sq14 w)) (F := fun a w => MUL a (MUL w w))
    (fun a w ha hw => ⟨canon14_mul14 _ _, by rw [sq14, pkm ha (canon14_mul14 w w), pkm hw hw]⟩)
    (wordG ()).reverse one14 (fun c hc => insp_word.1 c (List.mem_reverse.1 hc)) canon14_one14
  rw [List.map_reverse, insp_word.2, bone] at h
  exact h

theorem insp_gensX : (∀ c ∈ gensX, canon14 c = true) ∧ gensX.map pk = (List.range 5).map GX := by
  have e0 := gX_ok 0 (by simp [gensX])
  have e1 := gX_ok 1 (by simp [gensX])
  have e2 := gX_ok 2 (by simp [gensX])
  have e3 := gX_ok 3 (by simp [gensX])
  have e4 := gX_ok 4 (by simp [gensX])
  simp only [gensX, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4
  refine ⟨fun c hc => ?_, ?_⟩
  · simp only [gensX, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact e0.1
    · exact e1.1
    · exact e2.1
    · exact e3.1
    · exact e4.1
  · simp only [gensX, List.map_cons, List.map_nil, e0.2, e1.2, e2.2, e3.2, e4.2]
    rfl

theorem insp_c0 : c0 () = true := by
  have h := insp0_ok
  unfold c0K at h
  have hall : (k1s ++ k2s).all (· < elemsS.size) = true := by
    rw [tabS.1]
    decide
  have hany : (k2s.any fun b => es b == es 1) = k2s.any fun b => Nat.beq (XS b) (XS 1) :=
    any_congr' fun b hb => by
      rw [beq_pk (insp_es (insp_k2s b hb)).1 (insp_es (by omega)).1,
        (insp_es (insp_k2s b hb)).2, (insp_es (by omega)).2]
  unfold c0
  rw [hall, insp_closedL insp_k1s, insp_closedL insp_k2s,
    q8RelC_pk (insp_es (by omega)) (insp_es (by omega)),
    q8RelC_pk (insp_es (by omega)) (insp_es (by omega)), insp_sq (by omega), insp_sq (by omega),
    hany, h]
  rfl

theorem insp_c1 : c1 () = true := by
  rw [← insp1_ok]
  unfold c1 c1K
  refine all_congr' fun a ha => all_congr' fun b hb => ?_
  rw [q8RelC_pk (insp_es (List.mem_range.1 ha)) (insp_es (List.mem_range.1 hb))]

theorem insp_c2 : c2 () = true := by
  rw [← insp2_ok]
  unfold c2 c2K
  refine all_congr' fun ks hks => ?_
  have hk : ∀ a ∈ ks, a < 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hks
    rcases hks with rfl | rfl
    · exact insp_k1s
    · exact insp_k2s
  rw [← insp_gensX.2, List.all_map]
  refine all_congr' fun y hy => ?_
  have cy := insp_gensX.1 y hy
  rw [Function.comp_apply]
  refine all_congr' fun k hk' => any_congr' fun k' hk'' => ?_
  rw [beq_pk (canon14_mul14 _ _) (canon14_mul14 _ _), pkm cy (insp_es (hk k hk')).1,
    pkm (insp_es (hk k' hk'')).1 cy, (insp_es (hk k hk')).2, (insp_es (hk k' hk'')).2]

theorem insp_c3 : c3 () = true := by
  rw [← insp3_ok]
  obtain ⟨cg, pg⟩ := insp_g
  obtain ⟨cgi, pgi⟩ := insp_gi
  obtain ⟨c4, p4⟩ := insp_es (i := 4) (by omega)
  obtain ⟨c25, p25⟩ := insp_es (i := 25) (by omega)
  simp only [c3, c3K, sq14, bne]
  rw [insp_contains (canon14_mul14 _ _), insp_contains (canon14_mul14 _ _),
    beq_pk (canon14_mul14 _ _) canon14_one14, beq_pk (canon14_mul14 _ _) canon14_one14,
    beq_pk (canon14_mul14 _ _) canon14_one14, pkm (canon14_mul14 _ _) cgi, pkm cg c4,
    pkm (canon14_mul14 _ _) cgi, pkm cg c25, pkm cg cgi,
    pkm (canon14_mul14 _ _) (canon14_mul14 _ _), pkm c4 c4, bone, pg, pgi, p4, p25]

theorem insp_c4 : c4 () = true := by
  rw [← insp4_ok]
  obtain ⟨cg, pg⟩ := insp_g
  obtain ⟨cgi, pgi⟩ := insp_gi
  simp only [c4, c4K, sq14]
  rw [beq_pk bx0.1 (canon14_mul14 _ _), beq_pk by0.1 (canon14_mul14 _ _),
    pkm (canon14_mul14 (mul14 gc gc) (mul14 vc vc)) (canon14_mul14 gic gic),
    pkm (canon14_mul14 gc gc) (canon14_mul14 vc vc),
    pkm (canon14_mul14 (mul14 gic gic) uc) (canon14_mul14 gc gc), pkm (canon14_mul14 gic gic) bu.1,
    pkm cg cg, pkm cgi cgi, pkm bv.1 bv.1, bx0.2, by0.2, bu.2, bv.2,
    pg, pgi]

theorem ok543001 : c0 () = true ∧ c1 () = true ∧ c2 () = true ∧ c3 () = true ∧ c4 () = true :=
  ⟨insp_c0, insp_c1, insp_c2, insp_c3, insp_c4⟩

end CFSG.KD.G2Three

end
