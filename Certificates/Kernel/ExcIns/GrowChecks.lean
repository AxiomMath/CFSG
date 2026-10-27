module

public import Certificates.Data.Kernel.ExcIns.Grow
public import Certificates.Kernel.ExcExt.Data
public import Certificates.Kernel.ExcIns.Data0
public import Certificates.Kernel.ExcIns.Data2
public import Certificates.Kernel.ExcIns.Data3
public import Certificates.Kernel.ExcIns.Data4
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcInsK

open CFSG.ExcExtK

set_option maxRecDepth 100000

theorem ch712571gm : Nat.beq D0.gm 15 = true := by quickRfl
theorem ch712571nr : Nat.beq D0.nr 8 = true := by quickRfl
theorem ch712571pl : planesOK D.T0 81 D0.PL = true := by quickRfl
theorem ch712571rp : repsOK D0.R 8 24 = true := by quickRfl
theorem ch712571s : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr false 0 D0.S = true := by quickRfl
theorem ch712571g_0 : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true (ln128 D0.R 0) D0.G0 = true := by quickRfl
theorem ch712571g_1 : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true (ln128 D0.R 1) D0.G1 = true := by quickRfl
theorem ch712571g_2 : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true (ln128 D0.R 2) D0.G2 = true := by quickRfl
theorem ch712571g_3 : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true (ln128 D0.R 3) D0.G3 = true := by quickRfl
theorem ch712571g_4 : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true (ln128 D0.R 4) D0.G4 = true := by quickRfl
theorem ch712571g_5 : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true (ln128 D0.R 5) D0.G5 = true := by quickRfl
theorem ch712571g_6 : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true (ln128 D0.R 6) D0.G6 = true := by quickRfl
theorem ch712571g_7 : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true (ln128 D0.R 7) D0.G7 = true := by quickRfl

theorem ch712574gm : Nat.beq D2.gm 63 = true := by quickRfl
theorem ch712574nr : Nat.beq D2.nr 8 = true := by quickRfl
theorem ch712574pl : planesOK D.T2 729 D2.PL = true := by quickRfl
theorem ch712574rp : repsOK D2.R 8 36 = true := by quickRfl
theorem ch712574s : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr false 0 D2.S = true := by quickRfl
theorem ch712574g_0 : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true (ln128 D2.R 0) D2.G0 = true := by quickRfl
theorem ch712574g_1 : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true (ln128 D2.R 1) D2.G1 = true := by quickRfl
theorem ch712574g_2 : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true (ln128 D2.R 2) D2.G2 = true := by quickRfl
theorem ch712574g_3 : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true (ln128 D2.R 3) D2.G3 = true := by quickRfl
theorem ch712574g_4 : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true (ln128 D2.R 4) D2.G4 = true := by quickRfl
theorem ch712574g_5 : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true (ln128 D2.R 5) D2.G5 = true := by quickRfl
theorem ch712574g_6 : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true (ln128 D2.R 6) D2.G6 = true := by quickRfl
theorem ch712574g_7 : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true (ln128 D2.R 7) D2.G7 = true := by quickRfl

theorem ch712575gm : Nat.beq D3.gm 63 = true := by quickRfl
theorem ch712575nr : Nat.beq D3.nr 6 = true := by quickRfl
theorem ch712575pl : planesOK D.T3 243 D3.PL = true := by quickRfl
theorem ch712575rp : repsOK D3.R 6 36 = true := by quickRfl
theorem ch712575s : recsK D.T3 D3.PL 243 D3.gm D3.R D3.nr false 0 D3.S = true := by quickRfl
theorem ch712575g_0 : recsK D.T3 D3.PL 243 D3.gm D3.R D3.nr true (ln128 D3.R 0) D3.G0 = true := by quickRfl
theorem ch712575g_1 : recsK D.T3 D3.PL 243 D3.gm D3.R D3.nr true (ln128 D3.R 1) D3.G1 = true := by quickRfl
theorem ch712575g_2 : recsK D.T3 D3.PL 243 D3.gm D3.R D3.nr true (ln128 D3.R 2) D3.G2 = true := by quickRfl
theorem ch712575g_3 : recsK D.T3 D3.PL 243 D3.gm D3.R D3.nr true (ln128 D3.R 3) D3.G3 = true := by quickRfl
theorem ch712575g_4 : recsK D.T3 D3.PL 243 D3.gm D3.R D3.nr true (ln128 D3.R 4) D3.G4 = true := by quickRfl
theorem ch712575g_5 : recsK D.T3 D3.PL 243 D3.gm D3.R D3.nr true (ln128 D3.R 5) D3.G5 = true := by quickRfl

theorem ch712572gm : Nat.beq D4.gm 127 = true := by quickRfl
theorem ch712572nr : Nat.beq D4.nr 12 = true := by quickRfl
theorem ch712572pl : planesOK D.T4 2187 D4.PL = true := by quickRfl
theorem ch712572rp : repsOK D4.R 12 63 = true := by quickRfl
theorem ch712572s : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr false 0 D4.S = true := by quickRfl
theorem ch712572g_0 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 0) D4.G0 = true := by quickRfl
theorem ch712572g_1 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 1) D4.G1 = true := by quickRfl
theorem ch712572g_2 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 2) D4.G2 = true := by quickRfl
theorem ch712572g_3 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 3) D4.G3 = true := by quickRfl
theorem ch712572g_4 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 4) D4.G4 = true := by quickRfl
theorem ch712572g_5 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 5) D4.G5 = true := by quickRfl
theorem ch712572g_6 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 6) D4.G6 = true := by quickRfl
theorem ch712572g_7 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 7) D4.G7 = true := by quickRfl
theorem ch712572g_8 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 8) D4.G8 = true := by quickRfl
theorem ch712572g_9 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 9) D4.G9 = true := by quickRfl
theorem ch712572g_10 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 10) D4.G10 = true := by
  quickRfl
theorem ch712572g_11 : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true (ln128 D4.R 11) D4.G11 = true := by
  quickRfl

end CFSG.ExcInsK

end
