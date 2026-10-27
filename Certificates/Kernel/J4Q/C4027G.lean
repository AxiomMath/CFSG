module

public import Certificates.Kernel.J4Q.X0Base
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Sporadic.J4.QT2A

theorem xgens_chk : allR 8 (fun i => andB (andB (Nat.beq (mulJ c rm (getN one XG i) (getN one XG (i + 8))) one)
      (Nat.beq (mulJ c rm (getN one XG (i + 8)) (getN one XG i)) one))
    (Nat.beq (mulJ c rm (getN one XG i) (getN one XG 0)) (mulJ c rm (getN one XG 0) (getN one XG i)))) = true := by
  quickRfl

theorem xg0_chk : Nat.beq (getN one XG 0) (wordJ c rm one G5 G5i [1, 2, -3, 1, 2, -3]) = true := by quickRfl

theorem gens_ok : chkX0Gens = true := by
  have hs : x0GenRows.size = 8 := by
    rw [x0GenRows, x0Words_eq]
    rfl
  have hsi : x0InvRows.size = 8 := by
    simp [x0InvRows, hs]
  have hl : x0Words.length = 8 := by
    rw [x0Words_eq]
    rfl
  have h4 : eqRows (x0GenRows[0]!) (wR [1, 2, -3, 1, 2, -3]) = true := by
    rw [eqRows_of (x0Gen_enc (i := 0) (by decide)) (wR_enc _)]
    exact xg0_chk
  have h5 : ((List.range 8).all fun i => CFSG.Sporadic.J4.QT2.wfRows x0GenRows[i]! && CFSG.Sporadic.J4.QT2.wfRows x0InvRows[i]! &&
      eqRows (mulRows x0GenRows[i]! x0InvRows[i]!) idRows &&
      eqRows (mulRows x0InvRows[i]! x0GenRows[i]!) idRows &&
      eqRows (mulRows x0GenRows[i]! x0GenRows[0]!) (mulRows x0GenRows[0]! x0GenRows[i]!)) = true := by
    refine List.all_eq_true.2 fun i hi => ?_
    have hi' := List.mem_range.1 hi
    have hg := x0Gen_enc hi'
    have hv := x0Inv_enc hi'
    have h0 := x0Gen_enc (i := 0) (by decide)
    have k := allR_spec xgens_chk i hi'
    simp only [andB_eq, Bool.and_eq_true] at k
    have w1 : CFSG.Sporadic.J4.QT2.wfRows (x0GenRows[i]!) = true := wf_bool hg.1
    have w2 : CFSG.Sporadic.J4.QT2.wfRows (x0InvRows[i]!) = true := wf_bool hv.1
    rw [w1, w2, eqRows_of (mul_enc hK hg hv) (id_enc hK), eqRows_of (mul_enc hK hv hg) (id_enc hK),
      eqRows_of (mul_enc hK hg h0) (mul_enc hK h0 hg), k.1.1, k.1.2, k.2]
    rfl
  unfold chkX0Gens
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨hl, hs⟩, hsi⟩, h4⟩, h5⟩

end CertificateChecks.KernelJ4Q

end
