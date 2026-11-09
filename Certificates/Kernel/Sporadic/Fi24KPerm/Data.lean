module

import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24SevB
public import CFSG.Certificates.Kernel.Orders.He.Rels

#kc_repo #kc_json CFSG.KD.Fi24KPerm "Certificates/Kernel/Sporadic/Fi24KPerm/data/fk.json" 293063 17094973686673910520 (sl : List (Nat × List Nat × List Nat))

public section

namespace CFSG.KD.Fi24KPerm

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def U (k : Nat) : List Nat := findU sl k

@[expose] noncomputable def slCut : List Nat :=
  [0, 15, 24, 35, 41, 47, 52, 56, 57, 61, 66, 108, 119, 126, 132, 138, 145, 151, 158, 164, 170,
    176, 182, 188, 194, 199, 204, 205, 209, 210, 215, 216, 221, 226, 232, 238, 244, 250, 256,
    261, 266, 272, 278, 281, 283, 287, 289, 293, 296, 300, 302, 307, 309, 312, 314, 320, 326,
    332, 337, 342, 347, 353, 358, 364, 370, 374, 378, 383, 389, 395, 400, 405, 410, 415, 420,
    426, 432, 438, 442, 461, 471, 479, 486, 493, 499, 504, 510, 515, 521, 527, 532, 538, 544,
    550, 556, 561, 566, 571, 576, 577, 581, 583, 585, 591, 597, 603, 609, 614, 619, 625, 630,
    635, 640, 646, 650, 653, 656, 658, 660, 662, 667, 672, 678, 684, 690, 696, 702, 708, 714,
    720, 725, 727, 729, 734, 737, 741, 744, 747, 749, 752, 755, 757, 763, 769, 774, 779, 785,
    791, 796, 802, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822,
    826, 830, 834, 839, 845, 851, 857, 863, 869, 874, 879, 885, 890, 895, 901, 907, 913, 918,
    924, 930, 936, 941, 947, 953, 958, 964, 970, 976, 982, 988, 994, 1000, 1006, 1012, 1017,
    1022, 1028, 1034, 1040, 1046, 1051, 1056, 1062, 1068, 1073, 1079, 1085, 1091, 1096, 1101,
    1107, 1113, 1119, 1124, 1130, 1136, 1141, 1146, 1152, 1158, 1164, 1170, 1176, 1182, 1188,
    1194, 1200, 1206, 1212, 1218, 1224, 1230, 1236, 1242, 1248, 1253, 1259, 1265, 1270, 1275,
    1281, 1287, 1288, 1289, 1295, 1301, 1307, 1313, 1318, 1324, 1330, 1335, 1341, 1346, 1352,
    1358, 1364, 1369, 1375, 1380, 1385, 1391, 1397, 1403, 1409, 1415, 1421, 1427, 1433, 1439,
    1445, 1451, 1456, 1462, 1468, 1474, 1480, 1485, 1490, 1495, 1500, 1506, 1511, 1517, 1523,
    1528, 1534, 1540, 1546, 1551, 1557, 1562, 1567, 1573, 1578, 1583, 1588, 1593, 1599, 1605,
    1610, 1615, 1621, 1627, 1633, 1639, 1645, 1650, 1655, 1661, 1667, 1673, 1679, 1685, 1691,
    1697, 1703, 1709, 1715, 1721, 1727, 1733, 1738, 1744, 1746, 1747, 1748, 1749, 1750, 1752,
    1753, 1754, 1759, 1765, 1771, 1777, 1784, 1790, 1796, 1802, 1808, 1814, 1819, 1824, 1830,
    1835, 1840, 1846, 1852, 1858, 1864, 1870, 1876, 1881, 1887, 1893, 1899, 1905, 1911, 1916,
    1921, 1926, 1932, 1938, 1944, 1950, 1956, 1962, 1968, 1973, 1979, 1985, 1991, 1997, 2001,
    2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2015, 2021, 2026, 2032, 2037, 2042,
    2048, 2054, 2059, 2065, 2071, 2077, 2083, 2089, 2094, 2100, 2106, 2112, 2118, 2123, 2128,
    2133, 2139, 2144, 2149, 2155, 2160, 2166, 2172, 2178, 2184, 2190, 2196, 2202, 2207, 2213,
    2219, 2224, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2237, 2238, 2239, 2243, 2248, 2253,
    2259, 2264, 2270, 2276, 2281, 2287, 2292, 2298, 2304, 2309, 2315, 2320, 2326, 2332, 2338,
    2343, 2349, 2354, 2359, 2365, 2370, 2376, 2382, 2387, 2392, 2398, 2404, 2409, 2414, 2420,
    2426, 2432, 2437, 2443, 2449, 2455, 2461, 2466, 2471, 2476, 2480, 2481, 2482, 2483, 2484,
    2485, 2486, 2487, 2488, 2489, 2493, 2499, 2505, 2511, 2518, 2523, 2528, 2534, 2540, 2546,
    2552, 2558, 2563, 2569, 2574, 2580, 2586, 2592, 2598, 2604, 2610, 2616, 2622, 2627, 2633,
    2639, 2645, 2651, 2657, 2663, 2669, 2675, 2681, 2686, 2692, 2696, 2701, 2707, 2713, 2718,
    2720, 2721, 2722, 2723, 2724, 2725, 2727, 2728, 2729, 2734, 2740, 2746, 2752, 2758, 2764,
    2770, 2776, 2782, 2788, 2794, 2800, 2806, 2812, 2818, 2824, 2830, 2836, 2842, 2848, 2854,
    2860, 2865, 2870, 2875, 2881, 2887, 2893, 2898, 2904, 2909, 2915, 2921, 2927, 2933, 2938,
    2944, 2950, 2955, 2960, 2965, 2971, 2975, 2976, 2977, 2978, 2979, 2980, 2982, 2983, 2984,
    2989, 2995, 3001, 3007, 3013, 3019, 3026, 3032, 3038, 3044, 3050, 3056, 3062, 3068, 3074,
    3080, 3085, 3091, 3097, 3103, 3109, 3115, 3121, 3127, 3133, 3139, 3145, 3151, 3157, 3162,
    3168, 3174, 3180, 3186, 3192, 3198, 3204, 3210, 3216, 3219, 3220, 3221, 3222]

@[expose] noncomputable def slQ (i : Nat) : List (Nat × List Nat × List Nat) :=
  (sl.drop (nthD (nat_lit 0) slCut i)).take
    (Nat.sub (nthD (nat_lit 0) slCut (Nat.succ i)) (nthD (nat_lit 0) slCut i))

@[expose] noncomputable def bigL : List Nat :=
  [7, 26, 28, 30, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 246, 247,
    329, 330, 331, 332, 334, 335, 379, 381, 382, 383, 386, 387, 428, 429, 431, 432, 434, 435,
    480, 481, 483, 484, 487, 488, 530, 532, 533, 534, 536, 537, 581, 584, 585, 587, 588, 629,
    630, 631]

@[expose] noncomputable def slBig (i : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun k _ ih => orB (Nat.beq i k) ih) bigL

@[expose] noncomputable def slc (i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (slIn NW NT sl (slQ i)) (slInB NW NT sl (slQ i)) (slBig i))
    true (orB (Nat.beq i (nat_lit 246)) (Nat.beq i (nat_lit 247)))

@[expose] noncomputable def slcL (i : Nat) : Bool :=
  allL (fun e => allL (fun z => andB (Nat.ble (nat_lit 2) z) (orB (Nat.ble z (nat_lit 5))
    (andB (Nat.blt (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)) e.1)
      (hasU sl (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)))))) e.2.1) (slQ i)

@[expose] noncomputable def slcP (i b : Nat) : Bool :=
  allL (fun e => Nat.beq (ptCB NW NT (expU sl e.2.1) b) (ptCB NW NT e.2.2 b)) (slQ i)

@[expose] noncomputable def heL (ix iy : Nat) (v : List (Nat × Bool)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun l _ ih => Nat.add (Nat.mul (nat_lit 2)
      (Bool.rec (motive := fun _ => Nat) iy ix (Nat.beq l.1 (nat_lit 0))))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 1) (nat_lit 0) l.2) :: ih) v

@[expose] noncomputable def pureL (p : Nat × Nat × Nat × Nat × Nat × Nat) :
    List (List Nat × List Nat) :=
  (U p.2.2.2.1, U (nat_lit 64)) :: (U p.2.2.2.2.1, U (nat_lit 66)) ::
    (U p.2.2.2.2.2 ++ (U (nat_lit 64) ++ pw (U (nat_lit 66)) p.1),
      U (nat_lit 67) ++ U p.2.2.2.2.2) ::
    List.rec (motive := fun _ => List (List Nat × List Nat)) List.nil
      (fun v _ ih => (mW sl (heL p.2.1 p.2.2.1 v), List.nil) :: ih) CFSG.KD.OrdHe.rels

@[expose] noncomputable def pureT : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(1, 2211, 2215, 2540, 2541, 2542), (2, 2546, 2550, 2806, 2807, 2808),
    (3, 2812, 2816, 3078, 3079, 3080), (4, 3084, 3088, 3318, 3319, 3320),
    (5, 3324, 3328, 3573, 3574, 3575), (6, 3579, 3583, 3817, 3818, 3819)]

@[expose] noncomputable def fqL : List (List Nat × List Nat) :=
  (U (nat_lit 1085) ++ U (nat_lit 67), U (nat_lit 67) ++ U (nat_lit 1085)) ::
  (U (nat_lit 1086) ++ U (nat_lit 67), U (nat_lit 67) ++ U (nat_lit 1086)) ::
  (U (nat_lit 1082) ++ U (nat_lit 66), U (nat_lit 66) ++ U (nat_lit 1082)) ::
  (U (nat_lit 1083) ++ U (nat_lit 66), U (nat_lit 66) ++ U (nat_lit 1083)) ::
  (U (nat_lit 1084) ++ U (nat_lit 66), U (nat_lit 66) ++ U (nat_lit 1084)) ::
  (U (nat_lit 1655), U (nat_lit 0)) :: (U (nat_lit 1656), U (nat_lit 1)) ::
  (U (nat_lit 2206), U (nat_lit 0)) :: (U (nat_lit 2207), U (nat_lit 1)) ::
  List.rec (motive := fun _ => List (List Nat × List Nat)) List.nil
    (fun p _ ih => pureL p ++ ih) pureT

@[expose] noncomputable def fq (i : Nat) : List Nat × List Nat := nthD (List.nil, List.nil) fqL i

@[expose] noncomputable def fqc (i : Nat) : Bool := agB NW NT (fq i).1 (fq i).2

@[expose] noncomputable def fqP (i b : Nat) : Bool :=
  Nat.beq (ptCB NW NT (fq i).1 b) (ptCB NW NT (fq i).2 b)

@[expose] noncomputable def fNe : Bool :=
  neOK NW NT [(U (nat_lit 2211), []), (U (nat_lit 2546), []), (U (nat_lit 2812), []),
    (U (nat_lit 3084), []), (U (nat_lit 3324), []), (U (nat_lit 3579), [])]

end CFSG.KD.Fi24KPerm

end
