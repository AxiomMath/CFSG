module

public import Certificates.Data.Kernel.SmithL6KF
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataF

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem fWord_ok : fWordK tvc tcl wtd fs0 fe = true := by decide +kernel

theorem all_of_take_drop {α : Type} {f : α → Bool} (l : List α) (n : Nat)
    (h1 : (l.take n).all f = true) (h2 : (l.drop n).all f = true) : l.all f = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2]
  rfl

set_option maxHeartbeats 0 in
theorem fPlane_ok : fPlaneK tvc tcl fe fp = true := by
  unfold fPlaneK
  rw [Bool.and_eq_true]
  refine ⟨?_, all_of_take_drop _ 489 ?_ (all_of_take_drop _ 489 ?_
    (all_of_take_drop _ 489 ?_ ?_))⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end CertificateChecks.KernelSmithL6K
