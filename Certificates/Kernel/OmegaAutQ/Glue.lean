module

public import Certificates.Data.OmegaAutQ
public import Certificates.Data.Kernel.OmegaAutQ.Poly
public import Certificates.Kernel.OmegaAutQ.Data
import CFSG.Certificates.Kernel.OmegaAutQSound
import Certificates.Kernel.OmegaAutQ.Checks

public section

namespace CertificateChecks.KernelOmegaAutQ

open Certificates.OmegaAutQ CFSG.KD.OmegaAutQ CFSG.KC.OmegaAutQ

theorem chainPart_split {G : Type} [Mul G] [One G] [DecidableEq G] (Q I J : List G) (k : ℕ) :
    chainPartP Q I J = (chainPartP Q I (J.take k) && chainPartP Q I (J.drop k)) := by
  unfold chainPartP
  rw [← List.all_append, List.take_append_drop]

theorem tabA (k : ℕ) (hk : k < 8) (x : Fin 81) :
    (thetaHom ((q8List ()).getD k 1, 1) x).val = laneW 7 (W k) x.val := by
  have h : tabAChk k = true := by
    interval_cases k
    exacts [ch442008_a0, ch442008_a1, ch442008_a2, ch442008_a3, ch442008_a4, ch442008_a5,
      ch442008_a6, ch442008_a7]
  have := beq_iff_eq.1 (allLt_iff.1 h x.val x.isLt)
  simpa [Nat.mod_eq_of_lt x.isLt] using this

theorem tabB (l : ℕ) (hl : l < 8) (x : Fin 81) :
    (thetaHom (1, (q8List ()).getD l 1) x).val = laneW 7 (W (8 + l)) x.val := by
  have h : tabBChk l = true := by
    interval_cases l
    exacts [ch442008_b0, ch442008_b1, ch442008_b2, ch442008_b3, ch442008_b4, ch442008_b5,
      ch442008_b6, ch442008_b7]
  have := beq_iff_eq.1 (allLt_iff.1 h x.val x.isLt)
  simpa [Nat.mod_eq_of_lt x.isLt] using this

theorem check442008 : check () = true := by
  refine check_of (tA := W) (tB := fun l => W (8 + l)) (tP := W 16) (t := W 17) (e := 4) tabA tabB
    (beq_iff_eq.1 ch442008_dedup) ch442008_mul (by decide) ch442008_one ?_
  change chainPartP (lq (W 17) 4) iq iq = true
  rw [chainPart_split _ _ iq 5, chainPart_split _ _ (iq.drop 5) 5,
    chainPart_split _ _ ((iq.drop 5).drop 5) 5]
  simp only [ch442008_c1, ch442008_c2, ch442008_c3, ch442008_c4, Bool.and_self]

end CertificateChecks.KernelOmegaAutQ
