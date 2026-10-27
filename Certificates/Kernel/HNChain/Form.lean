module

public import Certificates.Kernel.HNChain.FormK
public import Certificates.Kernel.SporSch.HN.Seeds2106
public import CFSG.Certificates.Kernel.SporSch.HNF5ModSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.HNF5KronTSound
import CFSG.Certificates.Kernel.PackSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHNChain.Form

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelHNChain

theorem entK {K : Nat} (hK : K < 12) : Canon5 (sf K) ∧
    (HNF.OP K = 0 → Canon5 (sf (HNF.L K)) → Canon5 (sf (HNF.R K)) →
      ∀ i < 133, vm5 (sf (HNF.R K)) (sf (HNF.L K) i) = sf K i) ∧
    (HNF.OP K = 1 → ∀ i < 133, sf (HNF.L K) i = sf K i) ∧
    (HNF.OP K = 3 → Canon5 (sf (HNF.L K)) → ∀ i < 133, trRow5 (sf (HNF.L K)) i = sf K i) :=
  F5Kron.krBlkT_sound blk0 (Nat.zero_le K) (by omega)

theorem canon (k : Nat) (hk : k < 12) : Canon5 (sf k) := (entK hk).1

theorem specL {K : Nat} (hK : K < 12) : HNF.L K < 12 ∧ HNF.R K < 12 := by
  have hs := CFSG.KC.Pack.allN_spec specLt K hK
  rw [CFSG.KC.Pack.band_iff, Nat.blt_eq, Nat.blt_eq] at hs
  exact hs

theorem mulE {K l r : Nat} (hK : K < 12) (ho : HNF.OP K = 0) (hl : HNF.L K = l)
    (hr : HNF.R K = r) : ∀ i < 133, vm5 (sf r) (sf l i) = sf K i := by
  subst hl hr
  exact (entK hK).2.1 ho (canon _ (specL hK).1) (canon _ (specL hK).2)

theorem trE {K l : Nat} (hK : K < 12) (ho : HNF.OP K = 3) (hl : HNF.L K = l) :
    ∀ i < 133, trRow5 (sf l) i = sf K i := by
  subst hl
  exact (entK hK).2.2.2 ho (canon _ (specL hK).1)

theorem mul_eq {K l r : Nat} (hl1 : l < 12) (hr1 : r < 12) (hK : K < 12) (ho : HNF.OP K = 0)
    (hl : HNF.L K = l) (hr : HNF.R K = r) :
    mulM 5 133 (rows5 (sf l)) (rows5 (sf r)) = rows5 (sf K) :=
  mulM5_sound (canon l hl1) (canon r hr1) (mulE hK ho hl hr)

theorem eq_of {k l : Nat} (h : allN 133 (fun i => Nat.beq (sf k i) (sf l i)) = true) :
    rows5 (sf k) = rows5 (sf l) :=
  rows5_congr fun i hi => Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem rowsA_eq : rowsA = rows5 (sf 0) := by
  rw [HNSeeds.rowsA_eq]
  exact rows5_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec eqA i hi)).symm

theorem rowsB_eq : rowsB = rows5 (sf 1) := by
  rw [HNSeeds.rowsB_eq]
  exact rows5_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec eqB i hi)).symm

theorem rowsM_eq : rowsM = rows5 (sf 2) := by
  rw [rowsM, HNForm.eq]
  exact pay5_sound payM

theorem formFacts : formChecks rowsA rowsB rowsM = true := by
  have hMt : colsMat 133 (rows5 (sf 2)) = rows5 (sf 3) :=
    (trans5_sound (trE (K := 3) (l := 2) (by omega) rfl rfl)).1
  have hAt : colsMat 133 (rows5 (sf 0)) = rows5 (sf 6) :=
    (trans5_sound (trE (K := 6) (l := 0) (by omega) rfl rfl)).1
  have hBt : colsMat 133 (rows5 (sf 1)) = rows5 (sf 9) :=
    (trans5_sound (trE (K := 9) (l := 1) (by omega) rfl rfl)).1
  have hinv : (mulM 5 133 (rows5 (sf 2)) (invM 5 133 (rows5 (sf 2))) == idM 133) = true := by
    refine (inv5_sound (canon 2 (by omega)) (canon 4 (by omega)) fun i hi => ?_).1
    rw [mulE (K := 5) (l := 2) (r := 4) (by omega) rfl rfl rfl i hi]
    exact Nat.eq_of_beq_eq_true (allN_spec id5 i hi)
  have h7 := mul_eq (K := 7) (l := 6) (r := 2) (by omega) (by omega) (by omega) rfl rfl rfl
  have h8 := mul_eq (K := 8) (l := 7) (r := 0) (by omega) (by omega) (by omega) rfl rfl rfl
  have h10 := mul_eq (K := 10) (l := 9) (r := 2) (by omega) (by omega) (by omega) rfl rfl rfl
  have h11 := mul_eq (K := 11) (l := 10) (r := 1) (by omega) (by omega) (by omega) rfl rfl rfl
  unfold formChecks
  rw [rowsA_eq, rowsB_eq, rowsM_eq, hMt, eq_of sym, hinv, hAt, h7, h8, eq_of invA, hBt, h10, h11,
    eq_of invB]
  simp only [beq_self_eq_true, Bool.and_self]

end CertificateChecks.KernelHNChain.Form

end
