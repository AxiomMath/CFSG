module

public import Certificates.Kernel.MonsterExist.P5.OrbitCore
public import Certificates.Kernel.MonsterExist.P5.Roots

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

@[expose] def eSing : List Ent := [
  (189, 0, 0, 0), (192, 1, 0, 1), (198, 1, 0, 2), (119, 1, 0, 5), (201, 2, 1, 2), (219, 2, 1, 3),
  (122, 2, 1, 5), (199, 2, 2, 0), (225, 2, 2, 3), (128, 2, 2, 5), (38, 2, 3, 4), (202, 3, 4, 0),
  (174, 3, 4, 3), (131, 3, 4, 5), (237, 3, 5, 2), (57, 3, 5, 4), (149, 3, 5, 5), (41, 3, 6, 4),
  (226, 3, 7, 3), (126, 3, 7, 5), (231, 3, 8, 1), (63, 3, 8, 4), (155, 3, 8, 5), (47, 3, 9, 4),
  (11, 3, 10, 3), (175, 4, 11, 3), (129, 4, 11, 5), (177, 4, 12, 1), (183, 4, 12, 2), (93, 4, 12, 4),
  (104, 4, 12, 5), (50, 4, 13, 4), (239, 4, 14, 0), (75, 4, 14, 4), (140, 4, 14, 5), (232, 4, 18, 1),
  (235, 4, 18, 2), (64, 4, 18, 4), (153, 4, 18, 5), (45, 4, 19, 4), (69, 4, 20, 4), (161, 4, 20, 5),
  (178, 5, 25, 1), (166, 5, 25, 2), (94, 5, 25, 4), (102, 5, 25, 5), (48, 5, 26, 4), (186, 5, 27, 2),
  (96, 5, 27, 4), (107, 5, 27, 5), (185, 5, 28, 0), (86, 5, 28, 5), (77, 5, 31, 3), (139, 5, 32, 5),
  (241, 5, 35, 2), (70, 5, 35, 4), (159, 5, 35, 5), (73, 5, 36, 4), (135, 5, 36, 5), (42, 5, 40, 3),
  (169, 6, 42, 2), (97, 6, 42, 4), (105, 6, 42, 5), (167, 6, 43, 0), (85, 6, 43, 4), (188, 6, 47, 0),
  (89, 6, 47, 5), (123, 6, 48, 3), (214, 6, 54, 3), (79, 6, 54, 4), (141, 6, 54, 5), (43, 6, 55, 3),
  (19, 6, 57, 3), (33, 6, 59, 2), (170, 7, 60, 0), (196, 7, 60, 3), (88, 7, 60, 4), (124, 7, 61, 3),
  (114, 7, 67, 2), (197, 8, 74, 3)]

theorem kE_sing : chkE (encV vSing) eSing = true := by decide +kernel

theorem kNd_sing : (eSing.map Prod.fst).Nodup := by decide +kernel

theorem orbitFin_sing : orbitFin 12 vSing = (rkFibre 18).image encV :=
  orbit_eq vSing 18 eSing (by decide +kernel) rk_vSing kE_sing
    (by rw [card_rkFibre_18]; decide +kernel)
    kNd_sing

end CertificateChecks.MonsterExist.P5

end
