module

public import Certificates.Kernel.L34Syl.Data

public section

namespace CertificateChecks.KernelL34Syl

open CFSG.KC.L34Syl

theorem ch465003_orb0 :
    orbK 42 6 63 4398046511103 (lane 252 pm252 LS) 3 (hOf 42 4398046511103 OM0 OR0) OM0 OD0 56 =
      true := by
  decide +kernel

theorem ch465003_sub0 :
    subK 42 6 63 4398046511103 (lane 252 pm252 LM0) 3 OR0 CN0 (hOf 42 4398046511103 OM0 OR0)
      OM0 OD0 56 = true := by
  decide +kernel

theorem ch465003_lm0 : lettersOK 42 6 63 252 (lane 252 pm252 LM0) 3 = true := by decide +kernel

theorem ch465003_res0 :
    restrK 42 6 63 (lane 252 pm252 LM0) (lane 18 262143 SX0) HP0 (hOf 42 4398046511103 OM0 OR0) =
      true := by
  decide +kernel

theorem ch465003_sx0 : lettersOK 6 3 7 18 (lane 18 262143 SX0) 3 = true := by decide +kernel

theorem ch465003_st0 : grpK 6 3 7 18 262143 9 511 (lane 18 262143 SX0) 3 ST0 SD0 360 = true := by
  decide +kernel

theorem ch465003_cw0 :
    commsK 42 6 63 6 (lane 252 pm252 LM0) (fun i => lane 252 pm252 LM0 (Nat.mul 2 i)) CW0 0 =
      true := by
  decide +kernel

theorem ch465003_orb1 :
    orbK 42 6 63 4398046511103 (lane 252 pm252 LS) 3 (hOf 42 4398046511103 OM1 OR1) OM1 OD1 56 =
      true := by
  decide +kernel

theorem ch465003_sub1 :
    subK 42 6 63 4398046511103 (lane 252 pm252 LM1) 3 OR1 CN1 (hOf 42 4398046511103 OM1 OR1)
      OM1 OD1 56 = true := by
  decide +kernel

theorem ch465003_lm1 : lettersOK 42 6 63 252 (lane 252 pm252 LM1) 3 = true := by decide +kernel

theorem ch465003_res1 :
    restrK 42 6 63 (lane 252 pm252 LM1) (lane 18 262143 SX1) HP1 (hOf 42 4398046511103 OM1 OR1) =
      true := by
  decide +kernel

theorem ch465003_sx1 : lettersOK 6 3 7 18 (lane 18 262143 SX1) 3 = true := by decide +kernel

theorem ch465003_st1 : grpK 6 3 7 18 262143 9 511 (lane 18 262143 SX1) 3 ST1 SD1 360 = true := by
  decide +kernel

theorem ch465003_cw1 :
    commsK 42 6 63 6 (lane 252 pm252 LM1) (fun i => lane 252 pm252 LM1 (Nat.mul 2 i)) CW1 0 =
      true := by
  decide +kernel

theorem ch465003_orb2 :
    orbK 42 6 63 4398046511103 (lane 252 pm252 LS) 3 (hOf 42 4398046511103 OM2 OR2) OM2 OD2 56 =
      true := by
  decide +kernel

theorem ch465003_sub2 :
    subK 42 6 63 4398046511103 (lane 252 pm252 LM2) 3 OR2 CN2 (hOf 42 4398046511103 OM2 OR2)
      OM2 OD2 56 = true := by
  decide +kernel

theorem ch465003_lm2 : lettersOK 42 6 63 252 (lane 252 pm252 LM2) 3 = true := by decide +kernel

theorem ch465003_res2 :
    restrK 42 6 63 (lane 252 pm252 LM2) (lane 18 262143 SX2) HP2 (hOf 42 4398046511103 OM2 OR2) =
      true := by
  decide +kernel

theorem ch465003_sx2 : lettersOK 6 3 7 18 (lane 18 262143 SX2) 3 = true := by decide +kernel

theorem ch465003_st2 : grpK 6 3 7 18 262143 9 511 (lane 18 262143 SX2) 3 ST2 SD2 360 = true := by
  decide +kernel

theorem ch465003_cw2 :
    commsK 42 6 63 6 (lane 252 pm252 LM2) (fun i => lane 252 pm252 LM2 (Nat.mul 2 i)) CW2 0 =
      true := by
  decide +kernel

theorem ch465003_orb3 :
    orbK 42 6 63 4398046511103 (lane 252 pm252 LS) 3 (hOf 42 4398046511103 OM3 OR3) OM3 OD3 56 =
      true := by
  decide +kernel

theorem ch465003_sub3 :
    subK 42 6 63 4398046511103 (lane 252 pm252 LM3) 3 OR3 CN3 (hOf 42 4398046511103 OM3 OR3)
      OM3 OD3 56 = true := by
  decide +kernel

theorem ch465003_lm3 : lettersOK 42 6 63 252 (lane 252 pm252 LM3) 3 = true := by decide +kernel

theorem ch465003_res3 :
    restrK 42 6 63 (lane 252 pm252 LM3) (lane 18 262143 SX3) HP3 (hOf 42 4398046511103 OM3 OR3) =
      true := by
  decide +kernel

theorem ch465003_sx3 : lettersOK 6 3 7 18 (lane 18 262143 SX3) 3 = true := by decide +kernel

theorem ch465003_st3 : grpK 6 3 7 18 262143 9 511 (lane 18 262143 SX3) 3 ST3 SD3 360 = true := by
  decide +kernel

theorem ch465003_cw3 :
    commsK 42 6 63 6 (lane 252 pm252 LM3) (fun i => lane 252 pm252 LM3 (Nat.mul 2 i)) CW3 0 =
      true := by
  decide +kernel

theorem ch465003_orb4 :
    orbK 42 6 63 4398046511103 (lane 252 pm252 LS) 3 (hOf 42 4398046511103 OM4 OR4) OM4 OD4 56 =
      true := by
  decide +kernel

theorem ch465003_sub4 :
    subK 42 6 63 4398046511103 (lane 252 pm252 LM4) 3 OR4 CN4 (hOf 42 4398046511103 OM4 OR4)
      OM4 OD4 56 = true := by
  decide +kernel

theorem ch465003_lm4 : lettersOK 42 6 63 252 (lane 252 pm252 LM4) 3 = true := by decide +kernel

theorem ch465003_res4 :
    restrK 42 6 63 (lane 252 pm252 LM4) (lane 18 262143 SX4) HP4 (hOf 42 4398046511103 OM4 OR4) =
      true := by
  decide +kernel

theorem ch465003_sx4 : lettersOK 6 3 7 18 (lane 18 262143 SX4) 3 = true := by decide +kernel

theorem ch465003_st4 : grpK 6 3 7 18 262143 9 511 (lane 18 262143 SX4) 3 ST4 SD4 360 = true := by
  decide +kernel

theorem ch465003_cw4 :
    commsK 42 6 63 6 (lane 252 pm252 LM4) (fun i => lane 252 pm252 LM4 (Nat.mul 2 i)) CW4 0 =
      true := by
  decide +kernel

theorem ch465003_orb5 :
    orbK 42 6 63 4398046511103 (lane 252 pm252 LS) 3 (hOf 42 4398046511103 OM5 OR5) OM5 OD5 56 =
      true := by
  decide +kernel

theorem ch465003_sub5 :
    subK 42 6 63 4398046511103 (lane 252 pm252 LM5) 3 OR5 CN5 (hOf 42 4398046511103 OM5 OR5)
      OM5 OD5 56 = true := by
  decide +kernel

theorem ch465003_lm5 : lettersOK 42 6 63 252 (lane 252 pm252 LM5) 3 = true := by decide +kernel

theorem ch465003_res5 :
    restrK 42 6 63 (lane 252 pm252 LM5) (lane 18 262143 SX5) HP5 (hOf 42 4398046511103 OM5 OR5) =
      true := by
  decide +kernel

theorem ch465003_sx5 : lettersOK 6 3 7 18 (lane 18 262143 SX5) 3 = true := by decide +kernel

theorem ch465003_st5 : grpK 6 3 7 18 262143 9 511 (lane 18 262143 SX5) 3 ST5 SD5 360 = true := by
  decide +kernel

theorem ch465003_cw5 :
    commsK 42 6 63 6 (lane 252 pm252 LM5) (fun i => lane 252 pm252 LM5 (Nat.mul 2 i)) CW5 0 =
      true := by
  decide +kernel

end CertificateChecks.KernelL34Syl

end
