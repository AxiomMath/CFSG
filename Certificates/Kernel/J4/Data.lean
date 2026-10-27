module

public import Certificates.Data.Kernel.J4Run
public import CFSG.Certificates.Kernel.J4.MBSData
public import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_decls CFSG.KJ4.RUN "Certificates/Kernel/J4/data/RUN_const.txt" 4881817
  12155781860608135830

public section

namespace CFSG.KJ4.RUN

open CFSG.KJ4 CFSG.KJ4.R

@[expose] noncomputable def kd : KD where
  FT := KRS.FT
  HT := KRS.HT
  WT := KRS.WT
  RT := KRS.RT
  RZT := KRS.RZT
  PT := KRS.PT
  OT := KRS.OT
  CT := KRS.CT
  LT := KRS.LT
  EK := KRS.EK
  EN := KRS.EN
  ET0 := KRS.ET0
  ET := KRS.ET
  INV := KRS.INV
  TH := KRS.TH
  LET := KRS.LET
  TR1 := KRS.TR1
  PS1 := KRS.PS1
  W0 := KRS.W0
  PAW := KRS.PAW
  PBW := KRS.PBW
  W0W := KRS.W0W
  ND := KRS.ND
  NOM := KRS.NOM
  NF := 1775
  nH := 1432
  i0 := 575
  hx := 2
  hw := 1029
  sw := 0x3010301020102010301030103
  sn := 13
  cv := 4
  neK := 561
  neN := 272
  neT0 := 93
  neT := 309
  LVK := LVK
  LVN := LVN
  LVT0 := LVT0
  LVT := LVT
  BK := KRS.BK
  BN := KRS.BN
  BT := KRS.BT
  BT0 := KRS.BT0
  DCH := [(KRS.ED1, (368, (LVD1, KRS.BD1))), (KRS.ED2, (85, (LVD2, KRS.BD2))),
    (KRS.ED3, (36, (LVD3, KRS.BD3))), (KRS.ED4, (167, (LVD4, KRS.BD4))),
    (KRS.ED5, (67, (LVD5, KRS.BD5))), (KRS.ED6, (52, (LVD6, KRS.BD6)))]
  WREC := KShape.WREC
  CM := KShape.CM

@[expose] noncomputable def md : MD where
  FT := MBS.FT
  HT := MBS.HT
  WT := MBS.WT
  OT := MBS.OT
  SG := MBS.SG
  TW := MBS.TW
  ND := MBS.ND
  NOM := MBS.NOM
  NF := MBS.NF
  nH := 5969
  nSG := 186
  nW := 11
  ZW := MBS.ZW

end CFSG.KJ4.RUN

end
