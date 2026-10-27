module

public import Certificates.Data.Kernel.ExcIns.Wit
public import Certificates.Data.Kernel.ExcIns.Grow
public import Certificates.Kernel.ExcExt.Data
public import Certificates.Kernel.ExcIns.Data0
public import Certificates.Kernel.ExcIns.Data2
public import Certificates.Kernel.ExcIns.Data3
public import Certificates.Kernel.ExcIns.Data4
public import Certificates.Kernel.ExcIns.Data5
public import Certificates.Kernel.ExcIns.DataW
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcInsK

open CFSG.ExcExtK

set_option maxRecDepth 100000

theorem ch712571sg : sgnsFrom D.T0 W0.SG 4 0 = true := by quickRfl
theorem ch712571w_0 : repK D.T0 D.hx0 4 false (ln128 D0.R 0) W0.W0 = true := by quickRfl
theorem ch712571w_1 : repK D.T0 D.hx0 4 false (ln128 D0.R 1) W0.W1 = true := by quickRfl
theorem ch712571w_2 : repK D.T0 D.hx0 4 false (ln128 D0.R 2) W0.W2 = true := by quickRfl
theorem ch712571w_3 : repK D.T0 D.hx0 4 false (ln128 D0.R 3) W0.W3 = true := by quickRfl
theorem ch712571w_4 : repK D.T0 D.hx0 4 false (ln128 D0.R 4) W0.W4 = true := by quickRfl
theorem ch712571w_5 : repK D.T0 D.hx0 4 false (ln128 D0.R 5) W0.W5 = true := by quickRfl
theorem ch712571w_6 : repK D.T0 D.hx0 4 false (ln128 D0.R 6) W0.W6 = true := by quickRfl
theorem ch712571w_7 : repK D.T0 D.hx0 4 false (ln128 D0.R 7) W0.W7 = true := by quickRfl

theorem ch712574sg : sgnsFrom D.T2 W2.SG 6 0 = true := by quickRfl
theorem ch712574w_0 : repK D.T2 D.hx2 6 true (ln128 D2.R 0) W2.W0 = true := by quickRfl
theorem ch712574w_1 : repK D.T2 D.hx2 6 true (ln128 D2.R 1) W2.W1 = true := by quickRfl
theorem ch712574w_2 : repK D.T2 D.hx2 6 true (ln128 D2.R 2) W2.W2 = true := by quickRfl
theorem ch712574w_3 : repK D.T2 D.hx2 6 true (ln128 D2.R 3) W2.W3 = true := by quickRfl
theorem ch712574w_4 : repK D.T2 D.hx2 6 true (ln128 D2.R 4) W2.W4 = true := by quickRfl
theorem ch712574w_5 : repK D.T2 D.hx2 6 true (ln128 D2.R 5) W2.W5 = true := by quickRfl
theorem ch712574w_6 : repK D.T2 D.hx2 6 true (ln128 D2.R 6) W2.W6 = true := by quickRfl
theorem ch712574w_7 : repK D.T2 D.hx2 6 true (ln128 D2.R 7) W2.W7 = true := by quickRfl

theorem ch712575sg : sgnsFrom D.T3 W3.SG 6 0 = true := by quickRfl
theorem ch712575w_0 : repK D.T3 D.hx2 6 true (ln128 D3.R 0) W3.W0 = true := by quickRfl
theorem ch712575w_1 : repK D.T3 D.hx2 6 true (ln128 D3.R 1) W3.W1 = true := by quickRfl
theorem ch712575w_2 : repK D.T3 D.hx2 6 true (ln128 D3.R 2) W3.W2 = true := by quickRfl
theorem ch712575w_3 : repK D.T3 D.hx2 6 true (ln128 D3.R 3) W3.W3 = true := by quickRfl
theorem ch712575w_4 : repK D.T3 D.hx2 6 true (ln128 D3.R 4) W3.W4 = true := by quickRfl
theorem ch712575w_5 : repK D.T3 D.hx2 6 true (ln128 D3.R 5) W3.W5 = true := by quickRfl

theorem ch712572sg : sgnsFrom D.T4 W4.SG 7 0 = true := by quickRfl
theorem ch712572w_0 : repK D.T4 D.hx4 7 false (ln128 D4.R 0) W4.W0 = true := by quickRfl
theorem ch712572w_1 : repK D.T4 D.hx4 7 false (ln128 D4.R 1) W4.W1 = true := by quickRfl
theorem ch712572w_2 : repK D.T4 D.hx4 7 false (ln128 D4.R 2) W4.W2 = true := by quickRfl
theorem ch712572w_3 : repK D.T4 D.hx4 7 false (ln128 D4.R 3) W4.W3 = true := by quickRfl
theorem ch712572w_4 : repK D.T4 D.hx4 7 false (ln128 D4.R 4) W4.W4 = true := by quickRfl
theorem ch712572w_5 : repK D.T4 D.hx4 7 false (ln128 D4.R 5) W4.W5 = true := by quickRfl
theorem ch712572w_6 : repK D.T4 D.hx4 7 false (ln128 D4.R 6) W4.W6 = true := by quickRfl
theorem ch712572w_7 : repK D.T4 D.hx4 7 false (ln128 D4.R 7) W4.W7 = true := by quickRfl
theorem ch712572w_8 : repK D.T4 D.hx4 7 false (ln128 D4.R 8) W4.W8 = true := by quickRfl
theorem ch712572w_9 : repK D.T4 D.hx4 7 false (ln128 D4.R 9) W4.W9 = true := by quickRfl
theorem ch712572w_10 : repK D.T4 D.hx4 7 false (ln128 D4.R 10) W4.W10 = true := by quickRfl
theorem ch712572w_11 : repK D.T4 D.hx4 7 false (ln128 D4.R 11) W4.W11 = true := by quickRfl

theorem ch712573sg : sgnsFrom D.T5 W5.SG 8 0 = true := by quickRfl
theorem ch712573w_0 : repK D.T5 D.hx5 8 false (ln128 D5.R 0) W5.W0 = true := by quickRfl
theorem ch712573w_1 : repK D.T5 D.hx5 8 false (ln128 D5.R 1) W5.W1 = true := by quickRfl
theorem ch712573w_2 : repK D.T5 D.hx5 8 false (ln128 D5.R 2) W5.W2 = true := by quickRfl
theorem ch712573w_3 : repK D.T5 D.hx5 8 false (ln128 D5.R 3) W5.W3 = true := by quickRfl
theorem ch712573w_4 : repK D.T5 D.hx5 8 false (ln128 D5.R 4) W5.W4 = true := by quickRfl
theorem ch712573w_5 : repK D.T5 D.hx5 8 false (ln128 D5.R 5) W5.W5 = true := by quickRfl
theorem ch712573w_6 : repK D.T5 D.hx5 8 false (ln128 D5.R 6) W5.W6 = true := by quickRfl
theorem ch712573w_7 : repK D.T5 D.hx5 8 false (ln128 D5.R 7) W5.W7 = true := by quickRfl
theorem ch712573w_8 : repK D.T5 D.hx5 8 false (ln128 D5.R 8) W5.W8 = true := by quickRfl
theorem ch712573w_9 : repK D.T5 D.hx5 8 false (ln128 D5.R 9) W5.W9 = true := by quickRfl
theorem ch712573w_10 : repK D.T5 D.hx5 8 false (ln128 D5.R 10) W5.W10 = true := by quickRfl
theorem ch712573w_11 : repK D.T5 D.hx5 8 false (ln128 D5.R 11) W5.W11 = true := by quickRfl
theorem ch712573w_13 : repK D.T5 D.hx5 8 false (ln128 D5.R 13) W5.W13 = true := by quickRfl

end CFSG.ExcInsK

end
