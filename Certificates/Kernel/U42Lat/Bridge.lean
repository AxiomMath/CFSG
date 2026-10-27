module

public import Certificates.Kernel.U42Lat.Checks
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dU42Inputs
public import CFSG.Certificates.Kernel.Misc.PermClosWSound

public section

namespace CertificateChecks.KernelU42Lat.Glue

open Equiv CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW CFSG.KC.CosetLat
  CertificateChecks.KernelU42Lat CFSG.LocalAnalysis.RankThreeUC.S15.K21dU42Cert

set_option maxRecDepth 100000

theorem henc : ClosEnc (wcode (n := 45) 6) mU oneU := wcode_enc (by decide) (by decide)

theorem hT : ∀ j < 3, EL j = wcode 6 (tGens.getD j 1) := by decide +kernel

theorem hX : ∀ t < 5, EL (3 + t) = wcode 6 ((lat.getD t []).getD 3 1) := by decide +kernel

theorem hM : ∀ j < 2, EL (8 + j) = wcode 6 (mGens.getD j 1) := by decide +kernel

theorem hEA : EL 34 = wcode 6 ea := by decide +kernel

theorem hEB : EL 35 = wcode 6 eb := by decide +kernel

theorem hTG : ∀ j < tGens.length, EL j = wcode 6 (tGens.getD j 1) := hT

noncomputable abbrev T : Subgroup (Perm (Fin 45)) := Subgroup.closure {g | g ∈ tGens}

theorem tAt (k : ℕ) (hk : k < 64) :
    treeAt mU oneU EL tGens.length TE TP k = true ∧ sortAt 64 TE TS k = true ∧
      closedAt mU EL tGens.length 64 TE TC k = true := by
  obtain ⟨h1, h2⟩ := andB_eq_true ((allN_iff _ _).1 ch409001t k hk)
  obtain ⟨h2, h3⟩ := andB_eq_true h2
  exact ⟨h1, h2, h3⟩

theorem T_codes : ∀ k < 64, ∃ g ∈ T, wcode 6 g = TE k :=
  (clos_card henc tGens hTG (N := 64) (by decide) (fun k hk => (tAt k hk).1)
    (fun k hk => (tAt k hk).2.1)).1

theorem T_full : Nat.card T = 64 ∧ ∀ g ∈ T, ∃ k < 64, wcode 6 g = TE k :=
  (clos_card henc tGens hTG (N := 64) (by decide) (fun k hk => (tAt k hk).1)
    (fun k hk => (tAt k hk).2.1)).2.2 fun k hk => (tAt k hk).2.2

end CertificateChecks.KernelU42Lat.Glue

end
