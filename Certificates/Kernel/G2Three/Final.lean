module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import Certificates.Kernel.G2Three.Checks
public import Certificates.Kernel.G2Three.Parse
public import CFSG.Certificates.Kernel.G2Three.Tables
public import CFSG.Certificates.Kernel.G2Three.Pairs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open CFSG.KC.G2Three CFSG.KC.Ord CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U

theorem bx0 : canon14 x0c = true ∧ pk x0c = GA 0 := ⟨by quickRfl, Nat.eq_of_beq_eq_true (by quickRfl)⟩
theorem bx1 : canon14 x1c = true ∧ pk x1c = GA 1 := ⟨by quickRfl, Nat.eq_of_beq_eq_true (by quickRfl)⟩
theorem by0 : canon14 y0c = true ∧ pk y0c = GA 2 := ⟨by quickRfl, Nat.eq_of_beq_eq_true (by quickRfl)⟩
theorem by1 : canon14 y1c = true ∧ pk y1c = GA 3 := ⟨by quickRfl, Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem bone : pk one14 = ONE := Nat.eq_of_beq_eq_true (by quickRfl)

theorem sx0 : canon14 (sq14 x0c) = true ∧ pk (sq14 x0c) = MUL (GA 0) (GA 0) := mulE consts_ok bx0 bx0
theorem sx1 : canon14 (sq14 x1c) = true ∧ pk (sq14 x1c) = MUL (GA 1) (GA 1) := mulE consts_ok bx1 bx1
theorem sy0 : canon14 (sq14 y0c) = true ∧ pk (sq14 y0c) = MUL (GA 2) (GA 2) := mulE consts_ok by0 by0
theorem sy1 : canon14 (sq14 y1c) = true ∧ pk (sq14 y1c) = MUL (GA 3) (GA 3) := mulE consts_ok by1 by1

theorem btc : canon14 tc = true ∧ pk tc = XO 0 :=
  bindE (mulE consts_ok (mulE consts_ok (mulE consts_ok (mulE consts_ok sx1 by1) bx1) by1) sx1)
    (by quickRfl)

theorem bn1 : canon14 n1c = true ∧ pk n1c = GS 0 :=
  bindE (mulE consts_ok (mulE consts_ok bx1 sy1) bx1) (by quickRfl)

theorem buv : (canon14 uc = true ∧ pk uc = GX 2) ∧ (canon14 vc = true ∧ pk vc = GX 3) := by
  have bw := mulE consts_ok (mulE consts_ok (mulE consts_ok bx0 sy0) bx0)
    (mulE consts_ok (mulE consts_ok bx1 sy1) bx1)
  have bwi := mulE consts_ok (mulE consts_ok (mulE consts_ok sx1 by1) sx1)
    (mulE consts_ok (mulE consts_ok sx0 by0) sx0)
  exact ⟨bindE (mulE consts_ok (mulE consts_ok bw bx0) bwi) (by quickRfl),
    bindE (mulE consts_ok (mulE consts_ok bw by0) bwi) (by quickRfl)⟩

theorem bu : canon14 uc = true ∧ pk uc = GX 2 := buv.1

theorem bv : canon14 vc = true ∧ pk vc = GX 3 := buv.2

theorem bh0 : canon14 h0c = true ∧ pk h0c = GX 4 :=
  bindE (mulE consts_ok (mulE consts_ok (mulE consts_ok (mulE consts_ok sx0 by0) bx0) by0) sx0)
    (by quickRfl)

theorem bq2 : canon14 q2c = true ∧ pk q2c = GS 1 :=
  bindE (mulE consts_ok (mulE consts_ok bx1 bn1) sx1) (by quickRfl)

theorem bnb : canon14 nbc = true ∧ pk nbc = GS 2 :=
  bindE (mulE consts_ok (mulE consts_ok bu (mulE consts_ok bv bv)) bu) (by quickRfl)

theorem bqb2 : canon14 qb2c = true ∧ pk qb2c = GS 3 :=
  bindE (mulE consts_ok (mulE consts_ok bu bnb) (mulE consts_ok bu bu)) (by quickRfl)

theorem gX_ok : ∀ s < gensX.length,
    canon14 (gensX.getD s one14) = true ∧ pk (gensX.getD s one14) = GX s
  | 0, _ => bindE bx1 (by quickRfl)
  | 1, _ => bindE by1 (by quickRfl)
  | 2, _ => bu
  | 3, _ => bv
  | 4, _ => bh0
  | s + 5, h => absurd h (by simp [gensX])

theorem gS_ok : ∀ s < gensS.length,
    canon14 (gensS.getD s one14) = true ∧ pk (gensS.getD s one14) = GS s
  | 0, _ => bn1
  | 1, _ => bq2
  | 2, _ => bnb
  | 3, _ => bqb2
  | 4, _ => bindE bh0 (by quickRfl)
  | s + 5, h => absurd h (by simp [gensS])

theorem gP_ok : ∀ s < gensP.length,
    canon14 (gensP.getD s one14) = true ∧ pk (gensP.getD s one14) = GP s
  | 0, _ => bindE bx1 (by quickRfl)
  | 1, _ => bindE bu (by quickRfl)
  | s + 2, h => absurd h (by simp [gensP])

theorem gA_ok : ∀ s < 4,
    canon14 ([x0c, x1c, y0c, y1c].getD s one14) = true ∧ pk ([x0c, x1c, y0c, y1c].getD s one14) = GA s
  | 0, _ => bx0
  | 1, _ => bx1
  | 2, _ => by0
  | 3, _ => by1
  | s + 4, h => absurd h (by omega)

theorem gO_ok : ∀ s < gensO.length,
    (canon14 ((gensO.getD s (one14 ++ one14)).take 196) = true ∧
        pk ((gensO.getD s (one14 ++ one14)).take 196) = GA s) ∧
      (canon14 ((gensO.getD s (one14 ++ one14)).drop 196) = true ∧
        pk ((gensO.getD s (one14 ++ one14)).drop 196) = GB s)
  | 0, _ => take_drop_pair bx0 (bindE sx0 (by quickRfl))
  | 1, _ => take_drop_pair bx1 (bindE sx1 (by quickRfl))
  | 2, _ => take_drop_pair by0 (bindE sy0 (by quickRfl))
  | 3, _ => take_drop_pair by1 (bindE sy1 (by quickRfl))
  | s + 4, h => absurd h (by simp [gensO])

theorem one_facts : XX 0 = pk one14 ∧ XS 0 = pk one14 ∧ XP 0 = pk one14 := by
  have h := one_ok
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at h
  rw [bone]
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem tabX : elemsX.size = 576 ∧ closedCheck mul14 gensX elemsX = true ∧
    distinctCheck elemsX = true ∧ allCheck canon14 elemsX = true ∧
    ∀ t < 576, canon14 (elemsX.getD t []) = true ∧ pk (elemsX.getD t []) = XX t :=
  table_ok consts_ok (gens := gensX) (n := 576) (by decide) (by simp [gensX]) gX_ok
    one_facts.1 buildX_ok (by decide) stepX_ok (by simp [gensX]) sortX_ok (by decide)

theorem tabS : elemsS.size = 64 ∧ closedCheck mul14 gensS elemsS = true ∧
    distinctCheck elemsS = true ∧ allCheck canon14 elemsS = true ∧
    ∀ t < 64, canon14 (elemsS.getD t []) = true ∧ pk (elemsS.getD t []) = XS t :=
  table_ok consts_ok (gens := gensS) (n := 64) (by decide) (by simp [gensS]) gS_ok
    one_facts.2.1 buildS_ok (by decide) stepS_ok (by simp [gensS]) sortS_ok (by decide)

theorem tabP : elemsP.size = 9 ∧ closedCheck mul14 gensP elemsP = true ∧
    distinctCheck elemsP = true ∧ allCheck canon14 elemsP = true ∧
    ∀ t < 9, canon14 (elemsP.getD t []) = true ∧ pk (elemsP.getD t []) = XP t :=
  table_ok consts_ok (gens := gensP) (n := 9) (by decide) (by simp [gensP]) gP_ok
    one_facts.2.2 buildP_ok (by decide) stepP_ok (by simp [gensP]) sortP_ok (by decide)

theorem parO_eq : parO = (List.range 7370).map fun i => (OA i, OB i) := by
  have hO := orb_at orbO_ok (by decide)
  unfold parO
  rw [PO.eq]
  refine decodePairs_render (by decide) (fun i hi => ?_) parse_ok
  obtain ⟨h1, h2, -⟩ := hO i hi
  constructor <;> omega

theorem tabO : elemsO.size = 7371 ∧ distinctCheck elemsO = true ∧
    allCheck canon14 elemsO = true ∧
    ∀ t < 7371, canon14 (elemsO.getD t []) = true ∧ pk (elemsO.getD t []) = XO t :=
  orbit_ok consts_ok btc.1 (gps := gensO) (n := 7371) (by decide) gO_ok btc.2.symm
    (par := parO) (by rw [parO_eq]; simp)
    (fun i hi => by
      rw [parO_eq, List.getD_eq_getElem _ _ (by simpa using hi)]
      simp)
    orbO_ok (by decide) sortO_ok (by decide)

theorem okX : elemsX.size = 576 ∧ closedCheck mul14 gensX elemsX = true ∧
    distinctCheck elemsX = true ∧ allCheck canon14 elemsX = true ∧ commuteCheck = true := by
  obtain ⟨a, b, c, d, -⟩ := tabX
  refine ⟨a, b, c, d, ?_⟩
  unfold commuteCheck
  refine all_of_getD one14 fun s hs => ?_
  obtain ⟨cg, pg⟩ := gX_ok s hs
  have hb := allBelow_g2 comm_ok (by decide) s (by simpa [gensX] using hs)
  unfold commutes
  rw [beq_pk (canon14_mul14 _ _) (canon14_mul14 _ _), pk_mul14 consts_ok cg btc.1,
    pk_mul14 consts_ok btc.1 cg, pg, btc.2]
  exact hb

theorem okS : elemsS.size = 64 ∧ closedCheck mul14 gensS elemsS = true ∧
    distinctCheck elemsS = true ∧ allCheck canon14 elemsS = true := by
  obtain ⟨a, b, c, d, -⟩ := tabS
  exact ⟨a, b, c, d⟩

theorem okP : elemsP.size = 9 ∧ closedCheck mul14 gensP elemsP = true ∧
    distinctCheck elemsP = true ∧ allCheck canon14 elemsP = true := by
  obtain ⟨a, b, c, d, -⟩ := tabP
  exact ⟨a, b, c, d⟩

theorem okO : elemsO.size = 7371 ∧ distinctCheck elemsO = true ∧
    allCheck canon14 elemsO = true ∧ allCheck (invP (indexMap elemsO)) elemsS = true := by
  obtain ⟨a, b, c, d⟩ := tabO
  refine ⟨a, b, c, ?_⟩
  exact invTest_of consts_ok (S := elemsS) (O := elemsO) tabS.1 tabS.2.2.2.2 a d bone inv_ok
    (by decide)

theorem okC : allCheck centralP elemsX = true ∧ cubeCheck = true := by
  refine ⟨centTest_of consts_ok (gX_ok 0 (by simp [gensX])) bu btc tabX.1 tabX.2.2.2.2 bone
    cent_ok (by decide), ?_⟩
  unfold cubeCheck
  refine all_of_getD one14 fun s hs => ?_
  obtain ⟨cg, pg⟩ := gA_ok s (by simpa using hs)
  have hb := allBelow_g2 cube_ok (by decide) s (by simpa using hs)
  rw [sq14, beq_pk (canon14_mul14 _ _) canon14_one14, pk_mul14 consts_ok cg (canon14_mul14 _ _),
    pk_mul14 consts_ok cg cg, pg, bone]
  exact hb

end CFSG.KD.G2Three

end
