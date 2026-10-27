module

public import Certificates.Kernel.Sporadic.ONVec.Data
import CFSG.Certificates.Kernel.ONOut.InvVSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KS.ON CFSG.ONSchreier.Native

@[expose] noncomputable def gramV : Array CFSG.F3.Native.V :=
  Array.ofFn (n := 154) fun i => vOf (at0 GR i.val)

theorem allBelowN_eq (n : Nat) (p : Nat → Bool) : allBelowN n p = (List.range n).all p := by
  unfold allBelowN
  apply Bool.eq_iff_iff.2
  rw [Nat.all_eq_finRange_all, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, List.mem_range.1 hi⟩ (List.mem_finRange _)
  · intro h ⟨i, hi⟩ _
    exact h i (List.mem_range.2 hi)

theorem gramConnK : gramConnOK gramV (gramTree gramV).1 (gramTree gramV).2 = true := by
  unfold gramConnOK gramTree
  simp only [Id.run_bind, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    CFSG.KS.ONOut.InvV.ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure,
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero, allBelowN_eq]
  quickRfl

end CertificateChecks.KernelSpor.ONVec

end
