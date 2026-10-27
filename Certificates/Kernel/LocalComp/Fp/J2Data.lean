module

public import Certificates.Data.CFSGNative.Filter.Sec2

public section

namespace CFSG.KD.LC.Fp.J2D

open CFSG.SectionRank.Native

@[expose] def j2SecK : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/J2G1-f5r14B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/J2G1-f5r14B0.m2"
  nregs := 90
  prog := [
      .pow 2 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 0 5, .mul 5 1 6, .mul 6 0 7, .mul 7 2 8,
      .mul 8 0 9, .mul 9 2 10, .mul 10 0 11, .mul 11 1 12, .mul 0 2 13, .mul 13 0 14, .mul 14 2 15,
      .mul 15 0 16, .mul 16 1 17, .mul 17 0 18, .mul 18 2 19, .mul 19 0 20, .mul 20 2 21,
      .mul 21 0 22, .mul 22 1 23, .mul 23 0 24, .mul 24 1 25, .mul 25 0 26, .mul 26 2 27,
      .mul 27 0 28, .mul 28 1 29, .mul 29 0 30, .mul 30 1 31, .mul 31 0 32, .mul 1 0 33,
      .mul 33 1 34, .mul 34 0 35, .mul 35 2 36, .mul 36 0 37, .mul 37 1 38, .mul 38 0 39,
      .mul 39 2 40, .mul 40 0 41, .mul 41 2 42, .mul 42 0 43, .mul 43 1 44, .mul 44 0 45,
      .mul 45 2 46, .mul 46 0 47, .mul 47 2 48, .mul 48 0 49, .mul 49 1 50, .mul 50 0 51,
      .mul 51 1 52, .mul 52 0 53, .mul 53 2 54, .mul 54 0 55, .mul 55 2 56, .mul 0 1 57,
      .mul 57 0 58, .mul 58 2 59, .mul 59 0 60, .mul 60 1 61, .mul 61 0 62, .mul 62 2 63,
      .mul 63 0 64, .mul 64 1 65, .mul 65 0 66, .mul 66 1 67, .mul 67 0 68, .mul 68 2 69,
      .mul 69 0 70, .mul 70 2 71, .mul 71 0 72, .mul 72 1 73, .mul 73 0 74, .mul 74 1 75,
      .mul 75 0 76, .mul 76 2 77, .mul 77 0 78, .mul 78 2 79, .mul 79 0 80, .mul 80 1 81,
      .mul 81 0 82, .mul 82 2 83, .mul 83 0 84, .mul 84 1 85, .mul 85 0 86, .mul 86 2 87,
      .mul 87 0 88]
  outs := [12, 32, 56, 88]
  tReg := 89
  tests := List.range 14

end CFSG.KD.LC.Fp.J2D

end
