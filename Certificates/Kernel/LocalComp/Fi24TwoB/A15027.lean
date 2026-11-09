module

public import Certificates.Kernel.LocalComp.Fi24TwoB.Ch15027
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
public import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CertificateChecks.KernelSpor.Fi24C
open CertificateChecks.KernelSpor CertificateChecks.KernelLC
open CFSG.Sporadic.FischerOddCore (fi24KStrong)
open CFSG.RankThree.Native (commutatorA validA rep_of_validA)

@[expose] noncomputable def letK (z : Int) : Nat :=
  if z = 1 then Fi24KC.S 0 else if z = -1 then Fi24KC.SI 0 else if z = 2 then Fi24KC.S 1
  else Fi24KC.SI 1

@[expose] noncomputable def wordK (w : List Int) : Nat :=
  w.foldr (fun z t => pcomp 504 9 (mask 9) (letK z) t) (pidn 504 9)

theorem kIdK : idK 504 9 (mask 9) = true := by quickRfl

theorem kIdC : canonK 504 9 (mask 9) (504 * 9) (pidn 504 9) = true := by quickRfl

theorem strongK {j : Nat} (hj : j < 12) : fi24KStrong[j]! = unpack 504 9 (Fi24KC.S j) := by
  rw [kS]
  exact ofFn_get hj

theorem letter_eq (z : Int) : fi24KLetterA z = unpack 504 9 (letK z) ∧ Cn 504 9 (letK z) := by
  obtain ⟨c0, ci0, p0⟩ := cnK' 0 (by norm_num)
  obtain ⟨c1, ci1, p1⟩ := cnK' 1 (by norm_num)
  unfold fi24KLetterA letK
  split_ifs
  · exact ⟨strongK (by norm_num), c0⟩
  · rw [strongK (by norm_num)]
    exact ⟨(invEqK_sound p0).1, ci0⟩
  · exact ⟨strongK (by norm_num), c1⟩
  · rw [strongK (by norm_num)]
    exact ⟨(invEqK_sound p1).1, ci1⟩

theorem word_eq : ∀ w : List Int, fi24KWordA w = unpack 504 9 (wordK w) ∧ Cn 504 9 (wordK w)
  | [] => by
    rw [fi24KWordA_nil]
    exact ⟨(idK_sound kIdK).symm, kIdC⟩
  | z :: w => by
    obtain ⟨ih1, ih2⟩ := word_eq w
    obtain ⟨l1, l2⟩ := letter_eq z
    rw [fi24KWordA_cons, ih1, l1, compA_unpack l2 ih2]
    exact ⟨rfl, canonK_pcomp l2 ih2⟩

theorem kGen : allN 5 (fun k => Nat.beq (Fi24BKd.S k) (wordK fi24KdGenWords[k]!)) = true := by
  quickRfl

theorem kComm : allN 10 (fun m => Nat.beq (Fi24BKdd.S m)
    (pcomp 504 9 (mask 9) (pcomp 504 9 (mask 9) (Fi24BKd.S (fi24KdPairs[m]!).1)
      (Fi24BKd.S (fi24KdPairs[m]!).2))
      (pcomp 504 9 (mask 9) (Fi24BKd.SI (fi24KdPairs[m]!).1)
        (Fi24BKd.SI (fi24KdPairs[m]!).2)))) = true := by quickRfl

theorem kCanD : allN 16 (fun j => bAnd(canonK 504 9 (mask 9) (504 * 9) (Fi24BKd.S j),
    canonK 504 9 (mask 9) (504 * 9) (Fi24BKd.SI j))) = true := by quickRfl

theorem kCanDD : allN 21 (fun j => canonK 504 9 (mask 9) (504 * 9) (Fi24BKdd.S j)) = true := by
  quickRfl

theorem pairs_lt {m : Nat} (hm : m < 10) : (fi24KdPairs[m]!).1 < 5 ∧ (fi24KdPairs[m]!).2 < 5 := by
  interval_cases m <;> decide

theorem gens_ok : ∀ k < 5, eqA 504 fi24KdStrong[k]! (fi24KWordA fi24KdGenWords[k]!) = true := by
  intro k hk
  obtain ⟨w1, w2⟩ := word_eq fi24KdGenWords[k]!
  have hc := (bAnd_iff _ _).1 (allN_spec kCanD k (by omega))
  rw [dS, ofFn_get (by omega : k < 16), w1, eqA_unpack hc.1 w2]
  exact allN_spec kGen k hk

theorem comm_ok : ∀ m < 10, eqA 504 fi24KddStrong[m]! (commutatorA 504
    fi24KdStrong[(fi24KdPairs[m]!).1]! fi24KdStrong[(fi24KdPairs[m]!).2]!) = true := by
  intro m hm
  obtain ⟨ha, hb⟩ := pairs_lt hm
  generalize ea : (fi24KdPairs[m]!).1 = a at ha
  generalize eb : (fi24KdPairs[m]!).2 = b at hb
  have hm' := allN_spec kComm m hm
  simp only [ea, eb] at hm'
  have ca := (bAnd_iff _ _).1 (allN_spec kCanD a (by omega))
  have cb := (bAnd_iff _ _).1 (allN_spec kCanD b (by omega))
  have ia := (invEqK_sound (allN_spec permD a (by omega))).1
  have ib := (invEqK_sound (allN_spec permD b (by omega))).1
  unfold commutatorA
  rw [ddS, dS, ofFn_get (by omega : m < 21), ofFn_get (by omega : a < 16),
    ofFn_get (by omega : b < 16), ia, ib, compA_unpack ca.1 cb.1, compA_unpack ca.2 cb.2,
    compA_unpack (canonK_pcomp ca.1 cb.1) (canonK_pcomp ca.2 cb.2),
    eqA_unpack (allN_spec kCanDD m (by omega))
      (canonK_pcomp (canonK_pcomp ca.1 cb.1) (canonK_pcomp ca.2 cb.2))]
  exact hm'

@[expose] def fi24PbSwaps : List (Fin 378 × Fin 378) := [
    (0, 2), (2, 6), (6, 14), (14, 30), (30, 15), (15, 32), (32, 60), (60, 103), (103, 169),
    (1, 4), (4, 10), (10, 22), (22, 44), (44, 79), (79, 131), (131, 207), (207, 293), (293, 112),
    (3, 8), (8, 18), (18, 37), (37, 69), (5, 12), (12, 26), (26, 51), (51, 89), (89, 17),
    (17, 35), (35, 65), (65, 111), (111, 181), (7, 16), (16, 34), (34, 63), (63, 108), (108, 47),
    (47, 83), (83, 137), (137, 217), (217, 52), (9, 20), (20, 41), (41, 75), (75, 125),
    (125, 201), (201, 262), (262, 118), (118, 191), (191, 277), (11, 24), (24, 48), (48, 85),
    (85, 140), (140, 222), (222, 197), (197, 31), (31, 19), (19, 39), (13, 28), (28, 55),
    (55, 40), (40, 73), (73, 84), (84, 138), (138, 219), (219, 304), (304, 194), (21, 42),
    (42, 76), (76, 127), (127, 203), (203, 289), (289, 354), (354, 316), (316, 23), (23, 46),
    (25, 49), (49, 86), (86, 142), (142, 225), (225, 64), (64, 109), (109, 177), (177, 261),
    (261, 332), (27, 53), (53, 91), (91, 149), (149, 50), (50, 87), (87, 144), (144, 228),
    (228, 243), (243, 192), (29, 57), (57, 98), (98, 45), (45, 80), (80, 132), (132, 209),
    (209, 279), (279, 348), (348, 368), (33, 61), (61, 105), (105, 173), (173, 180), (180, 265),
    (265, 264), (264, 255), (255, 329), (329, 375), (36, 67), (67, 115), (115, 119), (119, 193),
    (193, 130), (130, 206), (206, 292), (292, 357), (357, 74), (38, 70), (70, 120), (120, 195),
    (195, 88), (88, 146), (146, 143), (143, 58), (58, 100), (100, 164), (43, 78), (78, 71),
    (71, 121), (121, 196), (196, 281), (281, 287), (287, 159), (159, 245), (245, 320), (54, 93),
    (93, 152), (152, 90), (90, 148), (148, 114), (114, 185), (185, 269), (269, 182), (182, 266),
    (56, 96), (96, 158), (158, 244), (244, 319), (319, 370), (370, 345), (345, 271), (271, 199),
    (199, 284), (59, 101), (101, 166), (166, 251), (251, 202), (62, 106), (106, 174), (174, 258),
    (258, 147), (147, 208), (208, 294), (294, 358), (358, 107), (107, 176), (66, 113), (113, 183),
    (183, 141), (141, 224), (224, 178), (178, 263), (263, 335), (335, 215), (215, 170), (68, 117),
    (117, 189), (189, 175), (175, 259), (259, 327), (327, 373), (373, 257), (257, 235),
    (235, 315), (72, 122), (122, 198), (198, 283), (283, 350), (350, 110), (110, 179), (179, 221),
    (221, 306), (306, 220), (77, 128), (128, 97), (97, 160), (160, 124), (124, 200), (200, 285),
    (285, 168), (168, 254), (254, 247), (81, 134), (134, 99), (99, 162), (162, 249), (249, 286),
    (286, 305), (305, 163), (163, 157), (157, 242), (82, 135), (135, 214), (214, 301), (301, 172),
    (172, 102), (102, 167), (167, 145), (145, 104), (104, 171), (92, 151), (151, 210), (210, 297),
    (297, 278), (278, 184), (184, 268), (268, 298), (298, 295), (295, 123), (94, 154), (154, 212),
    (212, 299), (299, 231), (231, 232), (232, 296), (296, 150), (150, 234), (234, 233), (95, 156),
    (156, 241), (241, 155), (155, 239), (239, 317), (317, 116), (116, 188), (188, 139),
    (139, 126), (129, 205), (205, 190), (190, 275), (275, 344), (344, 230), (230, 227),
    (227, 276), (276, 273), (273, 218), (133, 211), (136, 216), (216, 187), (187, 272),
    (272, 250), (250, 325), (325, 347), (347, 364), (364, 253), (253, 280), (153, 237),
    (237, 226), (226, 309), (309, 341), (341, 270), (270, 324), (324, 336), (336, 314),
    (314, 366), (161, 248), (248, 323), (323, 371), (371, 240), (240, 274), (274, 318),
    (318, 362), (362, 376), (376, 377), (165, 238), (238, 310), (310, 300), (300, 343),
    (186, 223), (223, 307), (307, 363), (363, 351), (351, 338), (338, 355), (355, 267),
    (267, 340), (340, 339), (213, 260), (260, 330), (330, 328), (328, 308), (308, 321),
    (321, 337), (337, 334), (334, 374), (374, 349), (229, 313), (313, 291), (291, 356),
    (356, 288), (288, 353), (353, 359), (359, 372), (372, 311), (311, 365), (236, 312),
    (312, 367), (367, 333), (333, 352), (246, 256), (256, 326), (326, 331), (331, 290),
    (252, 303), (303, 361), (361, 282), (282, 346), (302, 360), (360, 369), (369, 342),
    (342, 322)]

@[expose] def fi24SwapsN (L : List (Fin 378 × Fin 378)) (x : Nat) : Nat :=
  L.foldr (fun e y => if y == e.1.val then e.2.val else if y == e.2.val then e.1.val else y) x

theorem fi24SwapsN_val (L : List (Fin 378 × Fin 378)) (j : Fin 378) :
    ((L.map fun e => Equiv.swap e.1 e.2).prod j).val = fi24SwapsN L j.val := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    change _ = if fi24SwapsN L j.val == e.1.val then e.2.val else
      if fi24SwapsN L j.val == e.2.val then e.1.val else fi24SwapsN L j.val
    rw [← ih]
    split_ifs <;> simp_all [Fin.ext_iff]

theorem fi24Pb_swaps_chk : allN 378 (fun j => Nat.beq (fi24SwapsN fi24PbSwaps j)
    (pg 9 (mask 9) (Fi24PC.S 1) j)) = true := by
  quickRfl

theorem fi24Pb_swaps_pg (j : Fin 378) :
    ((fi24PbSwaps.map fun e => Equiv.swap e.1 e.2).prod j).val =
      pg 9 (mask 9) (Fi24PC.S 1) j.val := by
  rw [fi24SwapsN_val]
  exact Nat.eq_of_beq_eq_true (allN_spec fi24Pb_swaps_chk j.val j.2)

theorem fi24Pb_swaps :
    CFSG.Sporadic.FischerOddCore.fi24Pb = (fi24PbSwaps.map fun e => Equiv.swap e.1 e.2).prod := by
  ext j
  rw [fi24Pb_swaps_pg j, ← CFSG.Sporadic.FischerOddCore.rep_fi24Pb.apply j.2, pS,
    ofFn_get (by norm_num : 1 < 10), Orb.unpack_get j.2]

theorem sign_fi24Pb : Equiv.Perm.sign CFSG.Sporadic.FischerOddCore.fi24Pb = -1 := by
  have hne : fi24PbSwaps.all (fun e => !Nat.beq e.1.val e.2.val) = true := by
    decide +kernel
  have hlen : fi24PbSwaps.length = 335 := rfl
  rw [fi24Pb_swaps, Equiv.Perm.sign_prod_list_swap, List.length_map, hlen]
  · exact Odd.neg_one_pow ⟨167, rfl⟩
  · intro g hg
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
    have h := List.all_eq_true.1 hne e he
    refine ⟨e.1, e.2, fun h' => ?_, rfl⟩
    rw [h', Nat.beq_refl] at h
    exact absurd h (by decide)

open CFSG.Sporadic.FischerOddCore in
theorem card_fi24KdGen_le : Nat.card (Subgroup.closure (Set.range fun j : Fin (min 5
    fi24KdStrong.size) => permOfArr 504 fi24KdStrong[j.val]!)) ≤ 40131624960 := by
  obtain ⟨φ, hφ⟩ := exists_famHom (conjPerm.comp fi24K.subtype) fi24Sj_injective
    (fun h j => fi24K_conj_inv h.2 j)
  have hφ' : ∀ (h : ↥fi24K) j, fi24Sj (φ h j) = (h : Equiv.Perm (Fin 504)) * fi24Sj j *
      (h : Equiv.Perm (Fin 504))⁻¹ := hφ
  have hφb : φ ⟨fi24Sb, fi24Sb_mem⟩ = fi24Pb :=
    Equiv.ext fun j => fi24Sj_injective (by rw [hφ']; exact fi24Sj_conj_b j)
  have hψ : (Equiv.Perm.sign.comp φ) ⟨fi24Sb, fi24Sb_mem⟩ = -1 := by
    rw [MonoidHom.comp_apply, hφb, sign_fi24Pb]
  have hrange : (Equiv.Perm.sign.comp φ).range = ⊤ := by
    refine eq_top_iff.2 fun u _ => ?_
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨_, hψ⟩
  have hidx : (Equiv.Perm.sign.comp φ).ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hN : (((Equiv.Perm.sign.comp φ).ker.map fi24K.subtype).subgroupOf fi24K).index = 2 := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _),
      hidx]
  have hcomm := CFSG.ComponentClassification.RankTwoSporadic.commutator_le_of_relIndex_two hN
  have hcN : Nat.card ((Equiv.Perm.sign.comp φ).ker.map fi24K.subtype) = 40131624960 := by
    have h := Subgroup.card_mul_index (Equiv.Perm.sign.comp φ).ker
    rw [hidx, card_fi24K] at h
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    omega
  have hd := CFSG.KS.Raw.Orb.hd_of_head (Nat.min_le_right _ _) fi24KdHead
  have hle : Subgroup.closure (Set.range fun j : Fin (min 5 fi24KdStrong.size) =>
      permOfArr 504 fi24KdStrong[j.val]!) ≤ ⁅fi24K, fi24K⁆ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    have hk5 : k < 5 := lt_of_lt_of_le hk (Nat.min_le_left _ _)
    have hk' : k < fi24KdStrong.size := lt_of_lt_of_le hk (Nat.min_le_right _ _)
    have hv : validA 504 fi24KdStrong[k]! = true := by
      have := hd.inv k hk'
      rwa [rawInvs, map_getElem! hk'] at this
    change permOfArr 504 fi24KdStrong[k]! ∈ _
    rw [eq_of_eqA (rep_of_validA hv) (rep_fi24KWordA _) (gens_ok k hk5)]
    exact fi24KdGen_mem hk5
  rw [← hcN]
  exact Subgroup.card_le_of_le (hle.trans hcomm)

theorem chainD : rawChainOK 504 (fi24KdStrong.extract 0 (min 5 fi24KdStrong.size)) fi24KdStrong
    fi24KdBase.toArray fi24KdWords 4 = true := by
  refine Orb.rawChainOK_of_head_card 4 (Nat.min_le_right _ _) fi24KdHead ?_
  rw [sizesD]
  exact card_fi24KdGen_le

theorem chainsOK : fi24KdChainsOK = true := by
  unfold fi24KdChainsOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨by rw [sizeD]; norm_num, by rw [sizeDD]; norm_num⟩, chainD⟩, sizesD⟩, headDD⟩,
    sizesDD⟩, allLt_iff.2 gens_ok⟩, allLt_iff.2 comm_ok⟩

end CertificateChecks.KernelLC.Fi24B

end
