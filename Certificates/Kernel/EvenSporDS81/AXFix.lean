module

public import Certificates.Data.Kernel.EvenSporDS81.FCDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXData

public section

namespace CertificateChecks.KernelEvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.KC.EvenSporDS81

theorem axFixOKL_take_drop {ms : List (Array Nat)} {q : Nat → Bool} {fam : List (List Nat)}
    (n : Nat) (h1 : axFixOKL ms q (fam.take n) = true) (h2 : axFixOKL ms q (fam.drop n) = true) :
    axFixOKL ms q fam = true := by
  unfold axFixOKL at h1 h2 ⊢
  rw [← List.take_append_drop n fam, List.all_append, h1, h2] <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_fix0 : axFixOKL axMs.toList (fun k => axQs[k]!)
    (axFam.take 90) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_fix1 : axFixOKL axMs.toList (fun k => axQs[k]!)
    ((axFam.drop 90).take 90) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_fix2 : axFixOKL axMs.toList (fun k => axQs[k]!)
    (((axFam.drop 90).drop 90).take 90) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_fix3 : axFixOKL axMs.toList (fun k => axQs[k]!)
    ((((axFam.drop 90).drop 90).drop 90).take 90) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_fix4 : axFixOKL axMs.toList (fun k => axQs[k]!)
    (((((axFam.drop 90).drop 90).drop 90).drop 90).take 90) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_fix5 : axFixOKL axMs.toList (fun k => axQs[k]!)
    ((((((axFam.drop 90).drop 90).drop 90).drop 90).drop 90).take 90) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_fix6 : axFixOKL axMs.toList (fun k => axQs[k]!)
    (((((((axFam.drop 90).drop 90).drop 90).drop 90).drop 90).drop 90).take 90) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ax_fix7 : axFixOKL axMs.toList (fun k => axQs[k]!)
    (((((((axFam.drop 90).drop 90).drop 90).drop 90).drop 90).drop 90).drop 90) = true := by
  decide +kernel

theorem ax_fix : axFixOKL axMs.toList (fun k => axQs[k]!) axFam = true :=
  axFixOKL_take_drop 90 ax_fix0 <|
  axFixOKL_take_drop 90 ax_fix1 <|
  axFixOKL_take_drop 90 ax_fix2 <|
  axFixOKL_take_drop 90 ax_fix3 <|
  axFixOKL_take_drop 90 ax_fix4 <|
  axFixOKL_take_drop 90 ax_fix5 <|
  axFixOKL_take_drop 90 ax_fix6 <|
  ax_fix7

end CertificateChecks.KernelEvenSporDS81
