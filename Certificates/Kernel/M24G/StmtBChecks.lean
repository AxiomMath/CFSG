module

public import Certificates.Data.Kernel.M24G.StmtB
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.SliceIdx
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.StmtBC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem trio_lt : TL.all (fun t => (Native.octsT t).all (· < 2 ^ 24)) = true := by decide +kernel

theorem s310_p0 : (SliceGlue.slice (List.range Native.nTrio) (0 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p1 : (SliceGlue.slice (List.range Native.nTrio) (1 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p2 : (SliceGlue.slice (List.range Native.nTrio) (2 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p3 : (SliceGlue.slice (List.range Native.nTrio) (3 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p4 : (SliceGlue.slice (List.range Native.nTrio) (4 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p5 : (SliceGlue.slice (List.range Native.nTrio) (5 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p6 : (SliceGlue.slice (List.range Native.nTrio) (6 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p7 : (SliceGlue.slice (List.range Native.nTrio) (7 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p8 : (SliceGlue.slice (List.range Native.nTrio) (8 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p9 : (SliceGlue.slice (List.range Native.nTrio) (9 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p10 : (SliceGlue.slice (List.range Native.nTrio) (10 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p11 : (SliceGlue.slice (List.range Native.nTrio) (11 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p12 : (SliceGlue.slice (List.range Native.nTrio) (12 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p13 : (SliceGlue.slice (List.range Native.nTrio) (13 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p14 : (SliceGlue.slice (List.range Native.nTrio) (14 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p15 : (SliceGlue.slice (List.range Native.nTrio) (15 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p16 : (SliceGlue.slice (List.range Native.nTrio) (16 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p17 : (SliceGlue.slice (List.range Native.nTrio) (17 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p18 : (SliceGlue.slice (List.range Native.nTrio) (18 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p19 : (SliceGlue.slice (List.range Native.nTrio) (19 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p20 : (SliceGlue.slice (List.range Native.nTrio) (20 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p21 : (SliceGlue.slice (List.range Native.nTrio) (21 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p22 : (SliceGlue.slice (List.range Native.nTrio) (22 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p23 : (SliceGlue.slice (List.range Native.nTrio) (23 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p24 : (SliceGlue.slice (List.range Native.nTrio) (24 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p25 : (SliceGlue.slice (List.range Native.nTrio) (25 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p26 : (SliceGlue.slice (List.range Native.nTrio) (26 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p27 : (SliceGlue.slice (List.range Native.nTrio) (27 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p28 : (SliceGlue.slice (List.range Native.nTrio) (28 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p29 : (SliceGlue.slice (List.range Native.nTrio) (29 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p30 : (SliceGlue.slice (List.range Native.nTrio) (30 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p31 : (SliceGlue.slice (List.range Native.nTrio) (31 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p32 : (SliceGlue.slice (List.range Native.nTrio) (32 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p33 : (SliceGlue.slice (List.range Native.nTrio) (33 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p34 : (SliceGlue.slice (List.range Native.nTrio) (34 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p35 : (SliceGlue.slice (List.range Native.nTrio) (35 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p36 : (SliceGlue.slice (List.range Native.nTrio) (36 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p37 : (SliceGlue.slice (List.range Native.nTrio) (37 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p38 : (SliceGlue.slice (List.range Native.nTrio) (38 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p39 : (SliceGlue.slice (List.range Native.nTrio) (39 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p40 : (SliceGlue.slice (List.range Native.nTrio) (40 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p41 : (SliceGlue.slice (List.range Native.nTrio) (41 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p42 : (SliceGlue.slice (List.range Native.nTrio) (42 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p43 : (SliceGlue.slice (List.range Native.nTrio) (43 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310_p44 : (SliceGlue.slice (List.range Native.nTrio) (44 * 85) 85).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m) = true := by
  quickRfl

theorem s310 : stmt310K TL TS SL = true := by
  unfold stmt310K
  exact SliceGlue.all_of_slices _ 85 45 _ (Nat.le_of_ble_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => s310_p0
    | 1, _ => s310_p1
    | 2, _ => s310_p2
    | 3, _ => s310_p3
    | 4, _ => s310_p4
    | 5, _ => s310_p5
    | 6, _ => s310_p6
    | 7, _ => s310_p7
    | 8, _ => s310_p8
    | 9, _ => s310_p9
    | 10, _ => s310_p10
    | 11, _ => s310_p11
    | 12, _ => s310_p12
    | 13, _ => s310_p13
    | 14, _ => s310_p14
    | 15, _ => s310_p15
    | 16, _ => s310_p16
    | 17, _ => s310_p17
    | 18, _ => s310_p18
    | 19, _ => s310_p19
    | 20, _ => s310_p20
    | 21, _ => s310_p21
    | 22, _ => s310_p22
    | 23, _ => s310_p23
    | 24, _ => s310_p24
    | 25, _ => s310_p25
    | 26, _ => s310_p26
    | 27, _ => s310_p27
    | 28, _ => s310_p28
    | 29, _ => s310_p29
    | 30, _ => s310_p30
    | 31, _ => s310_p31
    | 32, _ => s310_p32
    | 33, _ => s310_p33
    | 34, _ => s310_p34
    | 35, _ => s310_p35
    | 36, _ => s310_p36
    | 37, _ => s310_p37
    | 38, _ => s310_p38
    | 39, _ => s310_p39
    | 40, _ => s310_p40
    | 41, _ => s310_p41
    | 42, _ => s310_p42
    | 43, _ => s310_p43
    | 44, _ => s310_p44
    | _ + 45, h => absurd h (by omega)

theorem s313_a0 : (SliceGlue.slice (List.range Native.nTrio) (0 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a1 : (SliceGlue.slice (List.range Native.nTrio) (1 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a2 : (SliceGlue.slice (List.range Native.nTrio) (2 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a3 : (SliceGlue.slice (List.range Native.nTrio) (3 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a4 : (SliceGlue.slice (List.range Native.nTrio) (4 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a5 : (SliceGlue.slice (List.range Native.nTrio) (5 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a6 : (SliceGlue.slice (List.range Native.nTrio) (6 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a7 : (SliceGlue.slice (List.range Native.nTrio) (7 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a8 : (SliceGlue.slice (List.range Native.nTrio) (8 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a9 : (SliceGlue.slice (List.range Native.nTrio) (9 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a10 : (SliceGlue.slice (List.range Native.nTrio) (10 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a11 : (SliceGlue.slice (List.range Native.nTrio) (11 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a12 : (SliceGlue.slice (List.range Native.nTrio) (12 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a13 : (SliceGlue.slice (List.range Native.nTrio) (13 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_a14 : (SliceGlue.slice (List.range Native.nTrio) (14 * 253) 253).all
    (fun p => !(oiK TL SL p 0) ||
      ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0).all
        fun m => Native.zc (trK TL m) (trK TL p) != 0) = true := by
  quickRfl

theorem s313_b0 : (SliceGlue.slice (List.range Native.nTrio) (0 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b1 : (SliceGlue.slice (List.range Native.nTrio) (1 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b2 : (SliceGlue.slice (List.range Native.nTrio) (2 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b3 : (SliceGlue.slice (List.range Native.nTrio) (3 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b4 : (SliceGlue.slice (List.range Native.nTrio) (4 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b5 : (SliceGlue.slice (List.range Native.nTrio) (5 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b6 : (SliceGlue.slice (List.range Native.nTrio) (6 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b7 : (SliceGlue.slice (List.range Native.nTrio) (7 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b8 : (SliceGlue.slice (List.range Native.nTrio) (8 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b9 : (SliceGlue.slice (List.range Native.nTrio) (9 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b10 : (SliceGlue.slice (List.range Native.nTrio) (10 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b11 : (SliceGlue.slice (List.range Native.nTrio) (11 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b12 : (SliceGlue.slice (List.range Native.nTrio) (12 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b13 : (SliceGlue.slice (List.range Native.nTrio) (13 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313_b14 : (SliceGlue.slice (List.range Native.nTrio) (14 * 253) 253).all
    (fun m => Native.zc (trK TL 0) (trK TL m) != 0 ||
      ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)) = true := by
  quickRfl

theorem s313 : stmt313K TL TS SL = true := by
  unfold stmt313K stmt313G
  rw [Bool.and_eq_true]
  exact ⟨SliceGlue.all_of_slices _ 253 15 _ (Nat.le_of_ble_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => s313_a0
    | 1, _ => s313_a1
    | 2, _ => s313_a2
    | 3, _ => s313_a3
    | 4, _ => s313_a4
    | 5, _ => s313_a5
    | 6, _ => s313_a6
    | 7, _ => s313_a7
    | 8, _ => s313_a8
    | 9, _ => s313_a9
    | 10, _ => s313_a10
    | 11, _ => s313_a11
    | 12, _ => s313_a12
    | 13, _ => s313_a13
    | 14, _ => s313_a14
    | _ + 15, h => absurd h (by omega),
    SliceGlue.all_of_slices _ 253 15 _ (Nat.le_of_ble_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => s313_b0
    | 1, _ => s313_b1
    | 2, _ => s313_b2
    | 3, _ => s313_b3
    | 4, _ => s313_b4
    | 5, _ => s313_b5
    | 6, _ => s313_b6
    | 7, _ => s313_b7
    | 8, _ => s313_b8
    | 9, _ => s313_b9
    | 10, _ => s313_b10
    | 11, _ => s313_b11
    | 12, _ => s313_b12
    | 13, _ => s313_b13
    | 14, _ => s313_b14
    | _ + 15, h => absurd h (by omega)⟩

end CFSG.KC.M24G.StmtBC
