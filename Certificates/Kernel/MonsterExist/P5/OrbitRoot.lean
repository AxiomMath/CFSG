module

public import Certificates.Kernel.MonsterExist.P5.OrbitCore
public import Certificates.Kernel.MonsterExist.P5.Roots

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

@[expose] def eRoot : List Ent := [
  (81, 0, 0, 0), (108, 1, 0, 3), (162, 1, 0, 4), (181, 1, 0, 5), (111, 2, 1, 1), (117, 2, 1, 2),
  (27, 2, 1, 4), (208, 2, 1, 5), (216, 2, 2, 3), (92, 2, 2, 5), (100, 2, 3, 4), (120, 3, 4, 2),
  (30, 3, 4, 4), (211, 3, 4, 5), (118, 3, 5, 0), (36, 3, 5, 4), (190, 3, 5, 5), (54, 3, 6, 3),
  (222, 3, 8, 1), (234, 3, 8, 2), (146, 3, 8, 5), (173, 3, 9, 4), (121, 4, 11, 0), (147, 4, 11, 3),
  (39, 4, 11, 4), (193, 4, 11, 5), (3, 4, 12, 3), (37, 4, 14, 4), (191, 4, 14, 5), (9, 4, 15, 3),
  (60, 4, 17, 1), (72, 4, 17, 2), (240, 4, 18, 2), (152, 4, 18, 5), (236, 4, 19, 0), (137, 4, 19, 5),
  (148, 5, 22, 3), (40, 5, 22, 4), (194, 5, 22, 5), (220, 5, 23, 5), (6, 5, 26, 1), (10, 5, 27, 3),
  (18, 5, 29, 2), (78, 5, 30, 2), (74, 5, 31, 0), (242, 5, 32, 0), (213, 5, 32, 3), (143, 5, 32, 5),
  (136, 5, 34, 5), (157, 6, 36, 2), (221, 6, 36, 5), (58, 6, 39, 4), (1, 6, 41, 2), (20, 6, 42, 0),
  (80, 6, 43, 0), (215, 6, 45, 3), (142, 6, 45, 5), (116, 6, 46, 5), (230, 7, 49, 5), (59, 7, 50, 4),
  (2, 7, 52, 0), (206, 7, 55, 2), (115, 7, 55, 5), (35, 7, 57, 4), (68, 8, 58, 4), (133, 8, 61, 5),
  (34, 8, 62, 4), (14, 9, 64, 3), (52, 9, 65, 4), (17, 10, 67, 1), (25, 10, 68, 3), (22, 11, 70, 1)]

theorem kE_root : chkE (encV vRoot) eRoot = true := by decide +kernel

theorem kNd_root : (eRoot.map Prod.fst).Nodup := by decide +kernel

theorem orbitFin_root : orbitFin 12 vRoot = (rkFibre 30).image encV :=
  orbit_eq vRoot 30 eRoot (by decide +kernel) rk_vRoot kE_root
    (by rw [card_rkFibre_30]; decide +kernel)
    kNd_root

end CertificateChecks.MonsterExist.P5

end
