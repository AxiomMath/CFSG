module

public import Certificates.Data.Kernel.PermCent.U33Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.U33T

open CFSG.GH74.KGroups.U33

theorem kuBeq22 (a b c d : CV 28) : (a * b == c * d) = eq22C a b c d := by
  rw [eq22C_eq, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]

theorem kuBeqPow1 (a : CV 28) (k : Nat) : (a ^ k == 1) = powOneC a k := by
  rw [powOneC_eq, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]

theorem kuBeqSq1 (a : CV 28) : (a * a == 1) = eq22C a a 1 1 := by
  rw [eq22C_eq, mul_one, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]

theorem kuConjB (g x y : CV 28) : decide (g * x * g⁻¹ = y) = eq22C g x y g := by
  rw [eq22C_eq, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, mul_inv_eq_iff_eq_mul]

@[expose] noncomputable def kuInvsF (L : List (CV 28)) : List (CV 28) :=
  L.filter fun s => eq22C s s 1 1 && s != 1

@[expose] noncomputable def kuO3F (L : List (CV 28)) : List (CV 28) :=
  L.filter fun x => powOneC x 3 && x != 1

theorem kuInvsF_eq (L : List (CV 28)) : invsOfC L = kuInvsF L := by
  simp only [invsOfC, kuInvsF, kuBeqSq1]

theorem kuO3F_eq (L : List (CV 28)) : o3OfC L = kuO3F L := by
  simp only [o3OfC, kuO3F, kuBeqPow1]

@[expose] noncomputable def kuX5gF (Cg I : List (CV 28)) (g : CV 28) : Bool :=
  I.all fun s => !eq22C g s s g ||
    Cg.any fun c => powOneC (s * (c * s * c⁻¹)) 3 && s * (c * s * c⁻¹) != 1

theorem kuX5gF_eq (Cg I : List (CV 28)) (g : CV 28) : x5gC Cg I g = kuX5gF Cg I g := by
  simp only [x5gC, kuX5gF, kuBeq22, kuBeqPow1]

@[expose] noncomputable def kuX5At (L I : List (CV 28)) (g : CV 28) : Bool :=
  if I.any (fun s => g * s == s * g) then x5gC (L.filter (fun c => g * c == c * g)) I g else true

@[expose] noncomputable def kuX5AtF (L I : List (CV 28)) (g : CV 28) : Bool :=
  if I.any (fun s => eq22C g s s g) then kuX5gF (L.filter (fun c => eq22C g c c g)) I g else true

theorem kuX5AtF_eq (L I : List (CV 28)) (g : CV 28) : kuX5AtF L I g = kuX5At L I g := by
  simp only [kuX5AtF, kuX5At, kuX5gF_eq, kuBeq22]

theorem k7137 : (cOf pa * cOf pb) ^ 7 = 1 ∧ cOf pa * cOf pb ≠ 1 ∧
    ((elemsC QP).filter fun g => (List.range 7).any fun i =>
      decide (g * (cOf pa * cOf pb) * g⁻¹ = (cOf pa * cOf pb) ^ i)).length = 21 := by
  simp only [kuConjB]
  decide +kernel

@[expose] noncomputable def kuNoInv (I : List (CV 28)) (x : CV 28) : Bool :=
  I.all fun s => !(x * s == s * x)

@[expose] noncomputable def kuF3At (I : List (CV 28)) (g h : CV 28) : Bool :=
  !(g * h == h * g && h != g && h != g * g) || [g, h, g * h, g * h * h].any fun x => kuNoInv I x

@[expose] noncomputable def kuF3AtF (I : List (CV 28)) (g h : CV 28) : Bool :=
  !(eq22C g h h g && h != g && h != g * g) ||
    [g, h, g * h, g * h * h].any fun x => I.all fun s => !eq22C x s s x

@[expose] noncomputable def kuF3RF (R I O : List (CV 28)) : Bool :=
  R.all fun g => O.all (kuF3AtF I g)

@[expose] noncomputable def kuConjN (a b : CV 28) : Nat → Nat → CV 28 → CV 28
  | 0, _, y => y
  | f + 1, k, y => if k ≤ 1 then y else
      kuConjN a b f (k / 2) (if k % 2 = 0 then a * y * a⁻¹ else b * y * b⁻¹)

@[expose] noncomputable def kuWordsF (a b : CV 28) (R : List (CV 28)) :
    List (CV 28) → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | g :: O, k :: W => R.contains (kuConjN a b k k g) && kuWordsF a b R O W

@[expose] def kuW3 : List Nat :=
  [1, 11, 12, 3290, 429, 301, 1878, 91, 1830, 15028, 1737, 346, 1225, 13995, 11606, 2411, 7461, 1,
    3436, 13674, 474, 13996, 2412, 1749, 301, 3435, 461, 7604, 9652, 661, 7340, 2345, 42157, 75,
    118, 9508, 10587, 6836, 409, 5801, 2395, 2666, 15211, 3498, 15029, 292, 1316, 22821, 2778,
    42572, 4772, 1899, 1322, 338, 230, 36, 5321, 1188, 26925, 1876, 2902, 10602, 1206, 602, 5548,
    1714, 164, 26185, 950, 947, 19286, 917, 937, 854, 6802, 596, 11433, 10585, 339, 586, 155, 19125,
    5, 851, 1874, 5267, 13493, 4820, 11563, 475, 82, 9653, 11437, 941, 2349, 809, 10645, 6730, 2770,
    19123, 3273, 4789, 10605, 5334, 18794, 169, 594, 1243, 4698, 53843, 660, 14041, 3730, 6582, 43,
    9509, 18795, 181, 3803, 10837, 6733, 19030, 659, 13465, 1882, 13997, 3658, 3753, 3492, 602,
    2890, 14921, 1323, 299, 410, 19306, 2340, 1901, 26922, 155, 875, 9, 22874, 5558, 2485, 237,
    5778, 21286, 3670, 6758, 948, 1746, 5418, 1877, 2410, 13739, 59684, 620, 173, 29, 293, 914, 470,
    5804, 13098, 949, 6949, 5333, 1317, 1865, 9941, 52, 333, 6994, 4781, 4780, 2413, 10, 29868,
    6875, 2667, 468, 297, 2662, 2889, 36, 18, 7, 2, 10642, 3373, 3365, 595, 1645, 13643, 3674, 877,
    614, 307, 2634, 19124, 2387, 852, 5705, 1875, 842, 1333, 661, 1170, 1835, 306, 3433, 10603,
    3499, 5718, 37478, 3657, 15020, 6803, 76, 38613, 202, 1427, 109, 1717, 22822, 3243, 37, 621,
    165, 939, 1837, 1900, 19, 205, 1445, 293, 2450, 7321, 42, 2390, 660, 7510, 19, 658, 59, 7349,
    45643, 26186, 106, 1193, 15013, 10667, 26923, 26987, 7019, 4, 1322, 1450, 426, 677, 587, 1197,
    13, 9515, 1708, 6546, 1637, 2854, 21078, 50, 148, 357, 1682, 874, 5293, 210, 2394, 5716, 434,
    42580, 90, 1172, 26, 692, 3497, 42, 84, 14642, 10838, 1707, 13901, 363, 9562, 333, 27337, 1718,
    330, 7506, 4754, 7513, 236, 13990, 859, 3748, 6549, 3509, 1171, 691, 420, 1388, 27994, 57, 44,
    83, 3, 172, 587, 612, 299, 22820, 7017, 425, 347, 3507, 1755, 105, 1753, 11602, 7507, 75, 13989,
    13513, 1828, 27478, 458, 2643, 873, 292, 21205, 4, 20, 38, 3766, 361, 10668, 234, 1705, 3434,
    13164, 693, 421, 42573, 1834, 86, 7020, 148, 74, 4969, 4821, 6835, 5292, 1385, 298, 91284, 153,
    84, 21, 76, 818, 6756, 6998, 228, 1638, 2779, 466, 5, 3510, 3508, 2644, 843, 603, 2900, 459, 27,
    5302, 2852, 620, 1426, 2853, 41, 457, 310, 74, 13988, 1636, 2386, 115, 2774, 3417, 9514, 1689,
    916, 2484, 11562, 21675, 21337, 54956, 10643, 1205, 1196, 6731, 666, 1716, 858, 933, 27347, 331,
    22, 109349, 307, 13461, 3379, 2660, 2777, 9561, 53, 42674, 84822, 11609, 6732, 2379, 166, 411,
    26921, 722, 13675, 469, 5556, 27285, 11081, 116, 726, 77, 37, 10, 3731, 7606, 11411, 3668, 938,
    5706, 11410, 438, 810, 356, 362, 9, 28, 43, 73, 28083, 844, 2858, 219, 4900, 330, 3757, 9369,
    82, 7605, 23212, 164, 2633, 1754, 150, 2486, 27286, 21206, 1686, 1451, 4684, 4755, 4970, 406,
    5708, 9642, 436, 7348, 853, 6866, 7514, 2650, 329, 14922, 404, 89, 1321, 5540, 1171, 13460,
    21211, 9563, 73, 1189, 108, 819, 21290, 217, 857, 13738, 203, 6996, 724, 1354, 38249, 11610,
    3750, 13668, 212, 585, 146, 86, 18, 3364, 45, 714, 1750, 676, 30422, 6837, 6995, 5419, 211,
    5322, 2859, 3475, 27979, 107, 1683, 22835, 13093, 9579, 13099, 213, 10669, 13673, 3401, 9643,
    7467, 331, 6867, 172, 6869, 6834, 820, 1172, 19028, 3501, 214, 204, 5300, 1748, 149, 6757,
    23213, 310, 114, 233, 45642, 13604, 3659, 25, 146, 915, 14934, 109348, 21, 2651, 102, 45670,
    218, 2378, 1833, 3366, 13642, 13993, 662, 716, 10836, 10665, 358, 1195, 1866, 1700, 868, 5805,
    4826, 876, 178, 1429, 405, 229, 300, 9397, 1881, 117, 2, 3378, 150, 345, 435, 11417, 6950, 1242,
    18739, 101, 437, 2661, 665, 1325, 6985, 14681, 850, 10539, 4788, 586, 3733, 1387, 4757, 58, 83,
    6821, 77, 166, 54933, 5301, 235, 7460, 6, 3763, 2377, 19307, 38251, 597, 822, 1444, 14923, 7315,
    725, 38, 3756, 5803, 180, 428, 598, 422, 1883, 2646, 6746, 1829, 297, 27466, 42411, 1709, 19019,
    41, 932, 3418, 4691, 76502, 51, 29842, 467, 38038, 15021, 149, 841, 694, 165, 427, 3291, 3755,
    5332, 1331, 13092, 14, 1386, 3660, 54674, 4758, 179, 6997, 1330, 3410, 13462, 2709, 13733, 5269,
    13732, 332, 5781, 585, 153, 20, 473, 1389, 3802, 2342, 7462, 1174, 1621, 713, 601, 2901, 918,
    3437, 9940, 3474, 3274, 11436, 29845, 54, 812, 173, 940, 7318, 11097]

@[expose] noncomputable def kuF3Cls (L : List (CV 28)) : Bool :=
  let I := kuInvsF L
  let O := kuO3F L
  let R := [O.getD 0 1, O.getD 17 1]
  kuF3RF R I O && R.all (kuX5AtF L I) && kuWordsF (cOf pa) (cOf pb) R O kuW3

theorem kuF3AtF_eq (I : List (CV 28)) (g h : CV 28) : kuF3AtF I g h = kuF3At I g h := by
  simp only [kuF3AtF, kuF3At, kuNoInv, kuBeq22]

theorem kuBeq_conj (c x y : CV 28) : (c * x * c⁻¹ == c * y * c⁻¹) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, mul_left_inj, mul_right_inj]

theorem kuNoInv_conj {I : List (CV 28)} {c : CV 28} (hI : ∀ s ∈ I, c * s * c⁻¹ ∈ I) (x : CV 28)
    (H : kuNoInv I (c * x * c⁻¹) = true) : kuNoInv I x = true := by
  simp only [kuNoInv, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_eq_false_iff_ne, ne_eq] at H ⊢
  intro s hs e
  apply H _ (hI s hs)
  have e1 : c * x * c⁻¹ * (c * s * c⁻¹) = c * (x * s) * c⁻¹ := by group
  have e2 : c * s * c⁻¹ * (c * x * c⁻¹) = c * (s * x) * c⁻¹ := by group
  rw [e1, e2, e]

theorem kuF3At_conj {I : List (CV 28)} {c : CV 28} (hI : ∀ s ∈ I, c * s * c⁻¹ ∈ I) (g h : CV 28)
    (H : kuF3At I (c * g * c⁻¹) (c * h * c⁻¹) = true) : kuF3At I g h = true := by
  have e4 : c * g * c⁻¹ * (c * h * c⁻¹) * (c * h * c⁻¹) = c * (g * h * h) * c⁻¹ := by group
  have e1 : c * g * c⁻¹ * (c * h * c⁻¹) = c * (g * h) * c⁻¹ := by group
  have e2 : c * h * c⁻¹ * (c * g * c⁻¹) = c * (h * g) * c⁻¹ := by group
  have e3 : c * g * c⁻¹ * (c * g * c⁻¹) = c * (g * g) * c⁻¹ := by group
  unfold kuF3At at H ⊢
  rw [e4, e1, e2, e3] at H
  cases hA : (g * h == h * g && h != g && h != g * g)
  · rfl
  · have hA' : (c * (g * h) * c⁻¹ == c * (h * g) * c⁻¹ && c * h * c⁻¹ != c * g * c⁻¹ &&
        c * h * c⁻¹ != c * (g * g) * c⁻¹) = true := by
      simpa only [bne, kuBeq_conj] using hA
    rw [hA', Bool.not_true, Bool.false_or] at H
    simp only [Bool.not_true, Bool.false_or, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true] at H ⊢
    rcases H with H | H | H | H
    · exact Or.inl (kuNoInv_conj hI _ H)
    · exact Or.inr (Or.inl (kuNoInv_conj hI _ H))
    · exact Or.inr (Or.inr (Or.inl (kuNoInv_conj hI _ H)))
    · exact Or.inr (Or.inr (Or.inr (kuNoInv_conj hI _ H)))

theorem kuF3_step {I O : List (CV 28)} {c : CV 28} (hI : ∀ s ∈ I, c * s * c⁻¹ ∈ I)
    (hO : ∀ h ∈ O, c * h * c⁻¹ ∈ O) {g : CV 28} (H : O.all (kuF3At I (c * g * c⁻¹)) = true) :
    O.all (kuF3At I g) = true := by
  rw [List.all_eq_true] at H ⊢
  exact fun h hh => kuF3At_conj hI g h (H _ (hO h hh))

theorem kuConjN_gen {Q : CV 28 → Prop} {a b : CV 28} (ha : ∀ y, Q (a * y * a⁻¹) → Q y)
    (hb : ∀ y, Q (b * y * b⁻¹) → Q y) (f : Nat) : ∀ k g, Q (kuConjN a b f k g) → Q g := by
  induction f with
  | zero => exact fun _ _ H => H
  | succ f ih =>
    intro k g H
    rw [kuConjN] at H
    split_ifs at H
    · exact H
    · exact ha _ (ih _ _ H)
    · exact hb _ (ih _ _ H)

theorem kuWords_gen {Q : CV 28 → Prop} {a b : CV 28} (ha : ∀ y, Q (a * y * a⁻¹) → Q y)
    (hb : ∀ y, Q (b * y * b⁻¹) → Q y) {R : List (CV 28)} (hR : ∀ r ∈ R, Q r) :
    ∀ (O : List (CV 28)) (W : List Nat), kuWordsF a b R O W = true → ∀ g ∈ O, Q g
  | [], _, _, _, hg => absurd hg List.not_mem_nil
  | _ :: _, [], hW, _, _ => by simp only [kuWordsF, Bool.false_eq_true] at hW
  | g :: O, k :: W, hW, x, hx => by
    rw [kuWordsF, Bool.and_eq_true, List.contains_iff_mem] at hW
    rcases List.mem_cons.1 hx with rfl | hx
    · exact kuConjN_gen ha hb k k x (hR _ hW.1)
    · exact kuWords_gen ha hb hR O W hW.2 x hx

theorem kuInvsF_conj {L : List (CV 28)} {c : CV 28} (hL : ∀ y ∈ L, c * y * c⁻¹ ∈ L) :
    ∀ s ∈ kuInvsF L, c * s * c⁻¹ ∈ kuInvsF L := by
  rw [← kuInvsF_eq]
  intro s hs
  simp only [invsOfC, List.mem_filter, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs ⊢
  have e : c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
  rw [e, hs.2.1, mul_one, mul_inv_cancel, conj_eq_one_iff]
  exact ⟨hL s hs.1, rfl, hs.2.2⟩

theorem kuO3F_conj {L : List (CV 28)} {c : CV 28} (hL : ∀ y ∈ L, c * y * c⁻¹ ∈ L) :
    ∀ x ∈ kuO3F L, c * x * c⁻¹ ∈ kuO3F L := by
  rw [← kuO3F_eq]
  intro x hx
  simp only [o3OfC, List.mem_filter, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hx ⊢
  rw [conj_pow, hx.2.1, mul_one, mul_inv_cancel, conj_eq_one_iff]
  exact ⟨hL x hx.1, rfl, hx.2.2⟩

theorem kuF3_of_cls {L : List (CV 28)} (ha : ∀ y ∈ L, cOf pa * y * (cOf pa)⁻¹ ∈ L)
    (hb : ∀ y ∈ L, cOf pb * y * (cOf pb)⁻¹ ∈ L) (H : kuF3Cls L = true) :
    f3C (invsOfC L) (o3OfC L) = true := by
  simp only [kuF3Cls, kuF3RF, Bool.and_eq_true, List.all_eq_true, kuF3AtF_eq] at H
  rw [kuInvsF_eq, kuO3F_eq]
  change (kuO3F L).all (fun g => (kuO3F L).all (kuF3At (kuInvsF L) g)) = true
  rw [List.all_eq_true]
  exact kuWords_gen (fun _ => kuF3_step (kuInvsF_conj ha) (kuO3F_conj ha))
    (fun _ => kuF3_step (kuInvsF_conj hb) (kuO3F_conj hb))
    (fun r hr => List.all_eq_true.2 (H.1.1 r hr)) _ _ H.2

theorem kF3C : kuF3Cls (elemsC QP) = true := by decide +kernel

@[expose] noncomputable def kuF1At (L : List (CV 28)) (s : CV 28) : Bool :=
  L.all fun g => !(g * s == s * g) || !(g ^ 7 == 1 && g != 1)

@[expose] noncomputable def kuF1AtF (L : List (CV 28)) (s : CV 28) : Bool :=
  L.all fun g => !eq22C g s s g || !(powOneC g 7 && g != 1)

@[expose] def kuW2 : List Nat :=
  [1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 19, 20, 21, 25, 27, 28, 29, 36, 37, 41, 45, 52, 53, 57, 59, 77,
    84, 85, 89, 91, 101, 105, 109, 148, 153, 165, 169, 173, 212, 229, 237, 293, 297, 340, 365, 404,
    409, 429, 468, 685, 724, 809, 877, 941, 1197, 1236, 1389, 1748, 1901, 2413, 2772, 2925, 3437]

@[expose] noncomputable def kuF1Cls (L : List (CV 28)) : Bool :=
  let S := kuW2.map fun k => kuConjN (cOf pa)⁻¹ (cOf pb)⁻¹ k k (cOf pu)
  kuF1AtF L (cOf pu) && (kuInvsF L).all fun s => S.contains s

theorem kuF1AtF_eq (L : List (CV 28)) (s : CV 28) : kuF1AtF L s = kuF1At L s := by
  simp only [kuF1AtF, kuF1At, kuBeq22, kuBeqPow1]

theorem kuF1At_conj {L : List (CV 28)} {c : CV 28} (hL : ∀ y ∈ L, c * y * c⁻¹ ∈ L) {s : CV 28}
    (H : kuF1At L s = true) : kuF1At L (c⁻¹ * s * c⁻¹⁻¹) = true := by
  have h1 : ∀ x : CV 28, (c * x * c⁻¹ == 1) = (x == 1) := fun x => by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, conj_eq_one_iff]
  simp only [kuF1At, List.all_eq_true] at H ⊢
  intro g hg
  have h := H _ (hL g hg)
  have e1 : c * g * c⁻¹ * s = c * (g * (c⁻¹ * s * c⁻¹⁻¹)) * c⁻¹ := by group
  have e2 : s * (c * g * c⁻¹) = c * (c⁻¹ * s * c⁻¹⁻¹ * g) * c⁻¹ := by group
  rw [e1, e2, kuBeq_conj, conj_pow] at h
  simpa only [bne, h1] using h

theorem kuConjN_F1 {L : List (CV 28)} {a b : CV 28} (ha : ∀ y ∈ L, a * y * a⁻¹ ∈ L)
    (hb : ∀ y ∈ L, b * y * b⁻¹ ∈ L) (f : Nat) :
    ∀ k y, kuF1At L y = true → kuF1At L (kuConjN a⁻¹ b⁻¹ f k y) = true := by
  induction f with
  | zero => exact fun _ _ H => H
  | succ f ih =>
    intro k y H
    rw [kuConjN]
    split_ifs
    · exact H
    · exact ih _ _ (kuF1At_conj ha H)
    · exact ih _ _ (kuF1At_conj hb H)

theorem kuF1_of_cls {L : List (CV 28)} (ha : ∀ y ∈ L, cOf pa * y * (cOf pa)⁻¹ ∈ L)
    (hb : ∀ y ∈ L, cOf pb * y * (cOf pb)⁻¹ ∈ L) (H : kuF1Cls L = true) :
    f1C L (invsOfC L) = true := by
  simp only [kuF1Cls, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    List.mem_map, kuF1AtF_eq] at H
  have hI : ∀ s ∈ invsOfC L, kuF1At L s = true := by
    rw [kuInvsF_eq]
    intro s hs
    obtain ⟨k, -, rfl⟩ := H.2 s hs
    exact kuConjN_F1 ha hb k k _ H.1
  rw [f1C, List.all_eq_true]
  intro g hg
  cases h7 : (g ^ 7 == 1 && g != 1)
  · rfl
  · rw [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro s hs
    have h := List.all_eq_true.1 (hI s hs) g hg
    rw [h7, Bool.not_true, Bool.or_false] at h
    exact h

theorem kF1C : kuF1Cls (elemsC QP) = true := by decide +kernel

theorem kuX5At_eq (L I : List (CV 28)) (g : CV 28) :
    kuX5At L I g = x5gC (L.filter (fun c => g * c == c * g)) I g := by
  unfold kuX5At
  split_ifs with h
  · rfl
  · simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at h
    symm
    simp only [x5gC, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    exact fun s hs => Or.inl (h s hs)

theorem kuX5At_conj {L I : List (CV 28)} {c : CV 28} (hL : ∀ y ∈ L, c⁻¹ * y * c⁻¹⁻¹ ∈ L)
    (hI : ∀ s ∈ I, c * s * c⁻¹ ∈ I) (g : CV 28) (H : kuX5At L I (c * g * c⁻¹) = true) :
    kuX5At L I g = true := by
  rw [kuX5At_eq] at H ⊢
  simp only [x5gC, List.all_eq_true, List.any_eq_true, List.mem_filter, Bool.or_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at H ⊢
  intro s hs
  rcases H _ (hI s hs) with h | ⟨d, ⟨hd, hdc⟩, h3, h1⟩
  · left
    intro e
    apply h
    have e1 : c * g * c⁻¹ * (c * s * c⁻¹) = c * (g * s) * c⁻¹ := by group
    have e2 : c * s * c⁻¹ * (c * g * c⁻¹) = c * (s * g) * c⁻¹ := by group
    rw [e1, e2, e]
  · right
    have key : s * (c⁻¹ * d * c⁻¹⁻¹ * s * (c⁻¹ * d * c⁻¹⁻¹)⁻¹) =
        c⁻¹ * (c * s * c⁻¹ * (d * (c * s * c⁻¹) * d⁻¹)) * c⁻¹⁻¹ := by group
    refine ⟨c⁻¹ * d * c⁻¹⁻¹, ⟨hL d hd, ?_⟩, ?_, ?_⟩
    · have e1 : g * (c⁻¹ * d * c⁻¹⁻¹) = c⁻¹ * (c * g * c⁻¹ * d) * c⁻¹⁻¹ := by group
      have e2 : c⁻¹ * d * c⁻¹⁻¹ * g = c⁻¹ * (d * (c * g * c⁻¹)) * c⁻¹⁻¹ := by group
      rw [e1, e2, hdc]
    · rw [key, conj_pow, h3, mul_one, mul_inv_cancel]
    · rw [key, conj_eq_one_iff]
      exact h1

theorem kuX5_of_cls {L : List (CV 28)} (ha : ∀ y ∈ L, cOf pa * y * (cOf pa)⁻¹ ∈ L)
    (hb : ∀ y ∈ L, cOf pb * y * (cOf pb)⁻¹ ∈ L)
    (ha' : ∀ y ∈ L, (cOf pa)⁻¹ * y * (cOf pa)⁻¹⁻¹ ∈ L)
    (hb' : ∀ y ∈ L, (cOf pb)⁻¹ * y * (cOf pb)⁻¹⁻¹ ∈ L) (H : kuF3Cls L = true) :
    x5C L (invsOfC L) (o3OfC L) = true := by
  simp only [kuF3Cls, Bool.and_eq_true, List.all_eq_true, kuX5AtF_eq] at H
  rw [kuInvsF_eq, kuO3F_eq]
  change (kuO3F L).all (kuX5At L (kuInvsF L)) = true
  rw [List.all_eq_true]
  exact kuWords_gen (kuX5At_conj ha' (kuInvsF_conj ha)) (kuX5At_conj hb' (kuInvsF_conj hb))
    H.1.2 _ _ H.2

theorem kuFoldRange {α : Type} (s : α → α) (x : α) (n : Nat) :
    (List.range n).foldl (fun L _ => s L) x = s^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Function.iterate_succ_apply']

@[expose] noncomputable def kuT0K : List (CV 28) :=
  (List.range 8).foldl (fun L _ => closureStepC
    [cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.ta,
      cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.tb] L) [1]

theorem kuT0_fix : (List.range 8).foldl (fun L _ => closureStepC
    [cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.ta,
      cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.tb] L) kuT0K = kuT0K := by
  decide +kernel

theorem kuT0_eq : t0LC = kuT0K := by
  have h := kuT0_fix
  unfold t0LC
  unfold kuT0K at h ⊢
  rw [kuFoldRange, kuFoldRange] at h
  have e : (40 : Nat) = 8 * 4 + 8 := rfl
  rw [kuFoldRange, kuFoldRange, e, Function.iterate_add_apply, Function.iterate_mul,
    Function.iterate_fixed h]

theorem kT0 : t0C = true := by
  rw [t0C, kuT0_eq]
  decide +kernel

theorem kZ : zC = true := by
  rw [zC, kuT0_eq]
  decide +kernel

theorem kuScan : (centerC && expC && cC && e1C) = true := by
  rw [centerC, expC, cC, e1C, kuT0_eq]
  simp only [kuBeq22, kuBeqPow1]
  decide +kernel

theorem kCenter : centerC = true := by
  have h := kuScan
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem kExp : expC = true := by
  have h := kuScan
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem kC : cC = true := by
  have h := kuScan
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem kE1 : e1C = true := by
  have h := kuScan
  simp only [Bool.and_eq_true] at h
  exact h.2

end CFSG.Certificates.Kernel.PkCV.U33T
