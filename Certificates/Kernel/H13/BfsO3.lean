module

public import CFSG.Quasithin.H13.L32NO3Inputs
public import CFSG.Certificates.Kernel.Mat8TSound
public import Certificates.Kernel.H13.Data

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.KC.Mat8P CFSG.KC.Mat8T

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem bfsOm3_P0 :
    layersT 16 65521 (o3G.map code64R) 100000 15 [oneP] [oneP] (D.om3L.drop 0) [] = true := by
  decide +kernel

theorem bfsOm3_bfs : elemsTC 16 65521 (o3G.map code64R) 100000 = (D.om3L, true) := by
  apply elemsTC_of_reach
  refine reach_layers 16 65521 _ _ _ 15 _ _ _ _ _ bfsOm3_P0 ?_
  exact reach_done' 65521 _ _ _ _ _ List.drop_zero

set_option maxHeartbeats 0 in
theorem bfsOm3F_P0 :
    layersT 16 65521 ((o3G ++ [fG]).map code64R) 100000 10 [oneP] [oneP] (D.om3FL.drop 1068) ((D.om3FL.drop 1068).take 988) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsOm3F_P1 :
    layersT 16 65521 ((o3G ++ [fG]).map code64R) 100000 6 (D.om3FL.drop 1068) ((D.om3FL.drop 1068).take 988) (D.om3FL.drop 0) [] = true := by
  decide +kernel

theorem bfsOm3F_bfs : elemsTC 16 65521 ((o3G ++ [fG]).map code64R) 100000 = (D.om3FL, true) := by
  apply elemsTC_of_reach
  refine reach_layers 16 65521 _ _ _ 10 _ _ _ _ _ bfsOm3F_P0 ?_
  refine reach_layers 16 65521 _ _ _ 6 _ _ _ _ _ bfsOm3F_P1 ?_
  exact reach_done' 65521 _ _ _ _ _ List.drop_zero

set_option maxHeartbeats 0 in
theorem bfsOmN_P0 :
    layersT 16 65521 ((o3G ++ [fG, sG]).map code64R) 100000 8 [oneP] [oneP] (D.omNL.drop 7808) ((D.omNL.drop 7808).take 2320) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsOmN_P1 :
    layersT 16 65521 ((o3G ++ [fG, sG]).map code64R) 100000 1 (D.omNL.drop 7808) ((D.omNL.drop 7808).take 2320) (D.omNL.drop 5333) ((D.omNL.drop 5333).take 2475) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsOmN_P2 :
    layersT 16 65521 ((o3G ++ [fG, sG]).map code64R) 100000 1 (D.omNL.drop 5333) ((D.omNL.drop 5333).take 2475) (D.omNL.drop 3124) ((D.omNL.drop 3124).take 2209) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsOmN_P3 :
    layersT 16 65521 ((o3G ++ [fG, sG]).map code64R) 100000 1 (D.omNL.drop 3124) ((D.omNL.drop 3124).take 2209) (D.omNL.drop 1502) ((D.omNL.drop 1502).take 1622) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsOmN_P4 :
    layersT 16 65521 ((o3G ++ [fG, sG]).map code64R) 100000 6 (D.omNL.drop 1502) ((D.omNL.drop 1502).take 1622) (D.omNL.drop 0) [] = true := by
  decide +kernel

theorem bfsOmN_bfs : elemsTC 16 65521 ((o3G ++ [fG, sG]).map code64R) 100000 = (D.omNL, true) := by
  apply elemsTC_of_reach
  refine reach_layers 16 65521 _ _ _ 8 _ _ _ _ _ bfsOmN_P0 ?_
  refine reach_layers 16 65521 _ _ _ 1 _ _ _ _ _ bfsOmN_P1 ?_
  refine reach_layers 16 65521 _ _ _ 1 _ _ _ _ _ bfsOmN_P2 ?_
  refine reach_layers 16 65521 _ _ _ 1 _ _ _ _ _ bfsOmN_P3 ?_
  refine reach_layers 16 65521 _ _ _ 6 _ _ _ _ _ bfsOmN_P4 ?_
  exact reach_done' 65521 _ _ _ _ _ List.drop_zero

set_option maxHeartbeats 0 in
theorem bfsH1_P0 :
    layersT 16 65521 ((o3G ++ [sG]).map code64R) 100000 10 [oneP] [oneP] (D.h1L.drop 1252) ((D.h1L.drop 1252).take 1032) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsH1_P1 :
    layersT 16 65521 ((o3G ++ [sG]).map code64R) 100000 6 (D.h1L.drop 1252) ((D.h1L.drop 1252).take 1032) (D.h1L.drop 0) [] = true := by
  decide +kernel

theorem bfsH1_bfs : elemsTC 16 65521 ((o3G ++ [sG]).map code64R) 100000 = (D.h1L, true) := by
  apply elemsTC_of_reach
  refine reach_layers 16 65521 _ _ _ 10 _ _ _ _ _ bfsH1_P0 ?_
  refine reach_layers 16 65521 _ _ _ 6 _ _ _ _ _ bfsH1_P1 ?_
  exact reach_done' 65521 _ _ _ _ _ List.drop_zero

set_option maxHeartbeats 0 in
theorem bfsH2_P0 :
    layersT 16 65521 ((o3G ++ [sfG]).map code64R) 100000 10 [oneP] [oneP] (D.h2L.drop 1068) ((D.h2L.drop 1068).take 988) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsH2_P1 :
    layersT 16 65521 ((o3G ++ [sfG]).map code64R) 100000 6 (D.h2L.drop 1068) ((D.h2L.drop 1068).take 988) (D.h2L.drop 0) [] = true := by
  decide +kernel

theorem bfsH2_bfs : elemsTC 16 65521 ((o3G ++ [sfG]).map code64R) 100000 = (D.h2L, true) := by
  apply elemsTC_of_reach
  refine reach_layers 16 65521 _ _ _ 10 _ _ _ _ _ bfsH2_P0 ?_
  refine reach_layers 16 65521 _ _ _ 6 _ _ _ _ _ bfsH2_P1 ?_
  exact reach_done' 65521 _ _ _ _ _ List.drop_zero

end CertificateChecks.KernelH13

end
