module

public import CFSG.Quasithin.H13.L32NS8Inputs
public import CFSG.Quasithin.H13.L32NS7Inputs
public import CFSG.Certificates.Kernel.Mat8TSound
public import Certificates.Kernel.H13.Data

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P CFSG.KC.Mat8T

set_option maxRecDepth 100000

theorem bfsS8_len : D.s8L.length < 100000 := by decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P0 :
    layersT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) 100000 7 [oneP] [oneP] (D.s8L.drop 34020) ((D.s8L.drop 34020).take 3746) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P1 :
    layersT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) 100000 1 (D.s8L.drop 34020) ((D.s8L.drop 34020).take 3746) (D.s8L.drop 26560) ((D.s8L.drop 26560).take 7460) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P2 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 26560) [] ((D.s8L.drop 26560).take 4657) (D.s8L.drop 18182) ((D.s8L.drop 18182).take 8378) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P3 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 18182) ((D.s8L.drop 18182).take 8378) ((D.s8L.drop 31217).take 2803) (D.s8L.drop 15402) ((D.s8L.drop 15402).take 11158) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P4 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 15402) [] ((D.s8L.drop 15402).take 3425) (D.s8L.drop 10481) ((D.s8L.drop 10481).take 4921) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P5 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 10481) ((D.s8L.drop 10481).take 4921) ((D.s8L.drop 18827).take 2978) (D.s8L.drop 7688) ((D.s8L.drop 7688).take 7714) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P6 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 7688) ((D.s8L.drop 7688).take 7714) ((D.s8L.drop 21805).take 2687) (D.s8L.drop 5866) ((D.s8L.drop 5866).take 9536) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P7 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 5866) ((D.s8L.drop 5866).take 9536) ((D.s8L.drop 24492).take 2068) (D.s8L.drop 4822) ((D.s8L.drop 4822).take 10580) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P8 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 4822) [] ((D.s8L.drop 4822).take 2206) (D.s8L.drop 2861) ((D.s8L.drop 2861).take 1961) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P9 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 2861) ((D.s8L.drop 2861).take 1961) ((D.s8L.drop 7028).take 2045) (D.s8L.drop 1854) ((D.s8L.drop 1854).take 2968) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P10 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 1854) ((D.s8L.drop 1854).take 2968) ((D.s8L.drop 9073).take 1936) (D.s8L.drop 1171) ((D.s8L.drop 1171).take 3651) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P11 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 1171) ((D.s8L.drop 1171).take 3651) ((D.s8L.drop 11009).take 1876) (D.s8L.drop 801) ((D.s8L.drop 801).take 4021) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P12 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 801) ((D.s8L.drop 801).take 4021) ((D.s8L.drop 12885).take 1847) (D.s8L.drop 619) ((D.s8L.drop 619).take 4203) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P13 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 619) ((D.s8L.drop 619).take 4203) ((D.s8L.drop 14732).take 670) (D.s8L.drop 568) ((D.s8L.drop 568).take 4254) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P14 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 568) [] ((D.s8L.drop 568).take 1763) (D.s8L.drop 89) ((D.s8L.drop 89).take 479) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P15 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 89) ((D.s8L.drop 89).take 479) ((D.s8L.drop 2331).take 1753) (D.s8L.drop 28) ((D.s8L.drop 28).take 540) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P16 :
    pieceT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) (D.s8L.drop 28) ((D.s8L.drop 28).take 540) ((D.s8L.drop 4084).take 738) (D.s8L.drop 21) ((D.s8L.drop 21).take 547) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsS8_P17 :
    layersT 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) 100000 2 (D.s8L.drop 21) ((D.s8L.drop 21).take 547) (D.s8L.drop 0) [] = true := by
  decide +kernel

theorem bfsS8_bfs : elemsTC 16 65521 (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) 100000 = (D.s8L, true) := by
  apply elemsTC_of_reach
  refine reach_layers 16 65521 _ _ _ 7 _ _ _ _ _ bfsS8_P0 ?_
  refine reach_layers 16 65521 _ _ _ 1 _ _ _ _ _ bfsS8_P1 ?_
  refine reach_layer' 65521 _ _ _ _ _ _ (ble_lenR _ _ bfsS8_len _) (by decide +kernel) ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 26560 4657 2803 _ bfsS8_P2 ?_
  refine mid_last 16 65521 _ _ _ _ _ _ _ _ _ bfsS8_P3 ?_
  refine reach_layer' 65521 _ _ _ _ _ _ (ble_lenR _ _ bfsS8_len _) (by decide +kernel) ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 15402 3425 7733 _ bfsS8_P4 ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 18827 2978 4755 _ bfsS8_P5 ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 21805 2687 2068 _ bfsS8_P6 ?_
  refine mid_last 16 65521 _ _ _ _ _ _ _ _ _ bfsS8_P7 ?_
  refine reach_layer' 65521 _ _ _ _ _ _ (ble_lenR _ _ bfsS8_len _) (by decide +kernel) ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 4822 2206 8374 _ bfsS8_P8 ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 7028 2045 6329 _ bfsS8_P9 ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 9073 1936 4393 _ bfsS8_P10 ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 11009 1876 2517 _ bfsS8_P11 ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 12885 1847 670 _ bfsS8_P12 ?_
  refine mid_last 16 65521 _ _ _ _ _ _ _ _ _ bfsS8_P13 ?_
  refine reach_layer' 65521 _ _ _ _ _ _ (ble_lenR _ _ bfsS8_len _) (by decide +kernel) ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 568 1763 2491 _ bfsS8_P14 ?_
  refine mid_chunk' 16 65521 _ _ _ _ _ _ _ _ 2331 1753 738 _ bfsS8_P15 ?_
  refine mid_last 16 65521 _ _ _ _ _ _ _ _ _ bfsS8_P16 ?_
  refine reach_layers 16 65521 _ _ _ 2 _ _ _ _ _ bfsS8_P17 ?_
  exact reach_done' 65521 _ _ _ _ _ List.drop_zero

set_option maxHeartbeats 0 in
theorem bfsS7_P0 :
    layersT 16 65521 (CFSG.Quasithin.H13.S7Cert.s7G.map code64R) 100000 11 [oneP] [oneP] (D.s7L.drop 0) [] = true := by
  decide +kernel

theorem bfsS7_bfs : elemsTC 16 65521 (CFSG.Quasithin.H13.S7Cert.s7G.map code64R) 100000 = (D.s7L, true) := by
  apply elemsTC_of_reach
  refine reach_layers 16 65521 _ _ _ 11 _ _ _ _ _ bfsS7_P0 ?_
  exact reach_done' 65521 _ _ _ _ _ List.drop_zero

end CertificateChecks.KernelH13

end
