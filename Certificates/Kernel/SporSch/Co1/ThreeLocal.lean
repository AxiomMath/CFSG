module

public import Certificates.Kernel.SporSch.Co1.Rows
public import CFSG.Certificates.Kernel.SporSch.Co1Inv
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1ThreeLocal

open CFSG.Sporadic.Co1Schreier.Native CFSG.KS.SporSch CertificateChecks.KernelSporSch.Co1Rows

@[expose] def CI : Rows := #[7956590, 8918352, 7114752, 16013521, 1157743, 14490962, 4993900,
  14243065, 4471858, 11713315, 13926120, 1078263, 2223090, 16075382, 4115107, 1976000, 11771923,
  6537648, 5751699, 11146384, 9698673, 11701973, 1932641, 16168021]

@[expose] def DI : Rows := #[5552954, 7412257, 11659329, 3505909, 11070474, 10880981, 14046710,
  13336905, 5328743, 14513321, 10619000, 11935052, 14083728, 16664421, 8310162, 7502737, 11848818,
  5817447, 9788922, 12813498, 2332640, 3661268, 3418159, 2012756]

@[expose] def YI : Rows := #[6073268, 1358335, 15255317, 4218932, 14481107, 4020518, 9544788,
  16164753, 3077268, 7721076, 4711750, 15493975, 9016171, 4589379, 12651910, 6875441, 16658876,
  4252742, 13698861, 11916794, 1341667, 2187071, 5353938, 12772422]

@[expose] def TI : Rows := #[10720186, 16262899, 5758288, 8301181, 12962088, 12253928, 4887596,
  1190346, 2532826, 12972677, 8197520, 4010035, 2245483, 14245366, 10485903, 11736115, 14017724,
  6444042, 9383027, 3318685, 15469080, 8084237, 5828854, 8287670]

@[expose] def C : Rows := mul RA RB

@[expose] def D : Rows := mul (mul RA RB) RB

@[expose] def U : Rows := mul (pow C 2) D

@[expose] def W : Rows := mul (pow U 2) C

@[expose] def X : Rows := mul (mul (pow CI 2) RA) (pow C 2)

@[expose] def Y : Rows := mul (mul (pow DI 2) (pow W 8)) (pow D 2)

@[expose] def T : Rows := mul (mul X Y) X

theorem kc : (wf C && wf CI && mul C CI == one ()) = true := by decide +kernel
theorem kd : (wf D && wf DI && mul D DI == one ()) = true := by decide +kernel
theorem ky : (wf Y && wf YI && mul Y YI == one ()) = true := by decide +kernel
theorem kt : (wf T && wf TI && mul T TI == one ()) = true := by decide +kernel

theorem aR_eq : aR = RA := rowsA_eq
theorem bR_eq : bR = RB := rowsB_eq

theorem cR_eq : cR = C := by
  unfold cR C
  rw [aR_eq, bR_eq]

theorem dR_eq : dR = D := by
  unfold dR D
  rw [aR_eq, bR_eq]

theorem inv_c : inv cR = CI := by
  rw [cR_eq]
  exact inv_eq_of_mul kc

theorem inv_d : inv dR = DI := by
  rw [dR_eq]
  exact inv_eq_of_mul kd

theorem yR_eq : yR = Y := by
  unfold yR wR uR Y W U
  rw [inv_d, cR_eq, dR_eq]

theorem tR_eq : tR = T := by
  unfold tR xR T X
  rw [yR_eq, inv_c, aR_eq, cR_eq]

theorem mulOne {X Y : Rows} (h : (wf X && wf Y && mul X Y == one ()) = true) :
    (mul X Y == one ()) = true := by
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem check : threeLocalCheck = true := by
  unfold threeLocalCheck
  rw [inv_c, inv_d, tR_eq, yR_eq, cR_eq, dR_eq, inv_eq_of_mul ky, inv_eq_of_mul kt]
  simp only [mulOne kc, mulOne kd, mulOne ky, mulOne kt, Bool.and_self]

end CertificateChecks.KernelSporSch.Co1ThreeLocal

end
