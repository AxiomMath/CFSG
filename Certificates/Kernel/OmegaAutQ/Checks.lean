module

public import Certificates.Data.OmegaAutQ
public import Certificates.Data.Kernel.OmegaAutQ.Poly
public import Certificates.Kernel.OmegaAutQ.Data

public section

namespace CertificateChecks.KernelOmegaAutQ

open Certificates.OmegaAutQ CFSG.KD.OmegaAutQ

@[expose] noncomputable def tabAChk (k : Nat) : Bool :=
  allLt 81 fun x => (thetaHom ((q8List ()).getD k 1, 1) ⟨x % 81, Nat.mod_lt _ (by decide)⟩).val ==
    laneW 7 (W k) x

@[expose] noncomputable def tabBChk (l : Nat) : Bool :=
  allLt 81 fun x => (thetaHom (1, (q8List ()).getD l 1) ⟨x % 81, Nat.mod_lt _ (by decide)⟩).val ==
    laneW 7 (W (8 + l)) x

theorem ch442008_a0 : tabAChk 0 = true := by decide +kernel
theorem ch442008_a1 : tabAChk 1 = true := by decide +kernel
theorem ch442008_a2 : tabAChk 2 = true := by decide +kernel
theorem ch442008_a3 : tabAChk 3 = true := by decide +kernel
theorem ch442008_a4 : tabAChk 4 = true := by decide +kernel
theorem ch442008_a5 : tabAChk 5 = true := by decide +kernel
theorem ch442008_a6 : tabAChk 6 = true := by decide +kernel
theorem ch442008_a7 : tabAChk 7 = true := by decide +kernel
theorem ch442008_b0 : tabBChk 0 = true := by decide +kernel
theorem ch442008_b1 : tabBChk 1 = true := by decide +kernel
theorem ch442008_b2 : tabBChk 2 = true := by decide +kernel
theorem ch442008_b3 : tabBChk 3 = true := by decide +kernel
theorem ch442008_b4 : tabBChk 4 = true := by decide +kernel
theorem ch442008_b5 : tabBChk 5 = true := by decide +kernel
theorem ch442008_b6 : tabBChk 6 = true := by decide +kernel
theorem ch442008_b7 : tabBChk 7 = true := by decide +kernel

theorem ch442008_dedup :
    (pairs64.pwFilter (fun p q => sigNe W (fun l => W (8 + l)) p q = true) ==
      (List.range 32).map (pairOf (W 16))) = true := by decide +kernel

theorem ch442008_mul : mulChk W (fun l => W (8 + l)) (W 16) (W 17) = true := by decide +kernel

theorem ch442008_one : oneChk W (fun l => W (8 + l)) (W 16) 4 = true := by decide +kernel

@[expose] noncomputable def iq : List (QT (W 17) 4) := invsOfP (lq (W 17) 4)

theorem ch442008_c1 : chainPartP (lq (W 17) 4) iq (iq.take 5) = true := by decide +kernel
theorem ch442008_c2 : chainPartP (lq (W 17) 4) iq ((iq.drop 5).take 5) = true := by decide +kernel
theorem ch442008_c3 : chainPartP (lq (W 17) 4) iq (((iq.drop 5).drop 5).take 5) = true := by
  decide +kernel
theorem ch442008_c4 : chainPartP (lq (W 17) 4) iq (((iq.drop 5).drop 5).drop 5) = true := by
  decide +kernel

end CertificateChecks.KernelOmegaAutQ
