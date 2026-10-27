module

public import Certificates.Data.M23Asl
public import Certificates.Data.Kernel.M23AslK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.M23Asl

open CFSG.KC.LQT.L CFSG.KC.M23Asl

@[expose] noncomputable def gYa : List Nat := [13524072217983629375053801568931081,
  26759172052226536161473753831225573, 28160362231756343230754668593326176,
  2921442598882893907702585546332596]

@[expose] noncomputable def gYb : List Nat := [13524072217983629375053801568931081,
  26759172052226536161473753831225573, 28160362231756343230754668593326176,
  1888069455180373144508806328618180]

@[expose] noncomputable def cXb : Nat := 1888069455180373144508806328618180

@[expose] noncomputable def gAa : List Nat :=
  [15144168925588342050858580562054697, 21191615460350747863401878740272427]

@[expose] noncomputable def gAb : List Nat :=
  [25209196429436661979843170338721824, 10643772104735624252285913095325092]

@[expose] noncomputable def gSa : List Nat := [122024278054565565571200, 394398422196286877246625]

@[expose] noncomputable def gSb : List Nat := [122024278054565565571200, 495970701014558310612225]

@[expose] noncomputable def tabS : List (Array Nat) :=
  [#[9, 8, 3, 2, 4, 16, 7, 6, 1, 0, 22, 11, 20, 21, 14, 15, 5, 17, 18, 19, 12, 13, 10],
   #[5, 7, 14, 17, 4, 16, 13, 2, 6, 0, 12, 22, 3, 11, 10, 18, 9, 1, 15, 8, 21, 19, 20],
   #[0, 3, 10, 1, 4, 9, 20, 7, 13, 5, 2, 11, 12, 8, 17, 18, 16, 14, 15, 19, 6, 22, 21]]

theorem ya : yxK 23 gYa 1920 cXb gAa (bfsK 23 gYa 32) = true := by quickRfl

theorem yb : yK 23 gYb 1920 gAb (bfsK 23 gYb 32) = true := by quickRfl

theorem da : diagK 23 16 32 gAa gSa 960 = true := by quickRfl

theorem db : diagK 23 16 32 gAb gSb 960 = true := by quickRfl

theorem tabs : (M23Asl.sgPerms.map M23Asl.tabP == tabS) = true := by quickRfl

theorem stabs : (CFSG.Quasithin.H.MathieuLat.m23STabs == tabS) = true := by quickRfl

end CFSG.KD.M23Asl

end
