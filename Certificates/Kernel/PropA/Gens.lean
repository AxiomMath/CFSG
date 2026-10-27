module

public import Certificates.Kernel.PropA.Classes
public import CFSG.Certificates.Kernel.Spor.PRecSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelPropA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.M12Std.PropA

@[expose] noncomputable def pa450010gK (b : Bool) (j : ℕ) : Equiv.Perm (Fin 28) :=
  [pA, pB, pG b, pT].getD j 1

@[expose] noncomputable def pa450010S (b : Bool) : ℕ → ℕ := if b then pa450010S2 else pa450010S1

@[expose] noncomputable def pa450010SI (b : Bool) : ℕ → ℕ :=
  if b then pa450010S2I else pa450010S1I

@[expose] def pa450010tabs (b : Bool) : List Table :=
  [Data.tabA, Data.tabB, if b then Data.tabG2 else Data.tabG1, Data.tabT]

theorem pa450010_tabs1 : allN 4 (fun j => allN 28 (fun i =>
    Nat.beq (pg 5 (mask 5) (pa450010S1 j) i) (ap ((pa450010tabs false).getD j #[]) i))) = true := by
  quickRfl

theorem pa450010_tabs2 : allN 4 (fun j => allN 28 (fun i =>
    Nat.beq (pg 5 (mask 5) (pa450010S2 j) i) (ap ((pa450010tabs true).getD j #[]) i))) = true := by
  quickRfl

theorem pa450010_tabs (b : Bool) : allN 4 (fun j => allN 28 (fun i =>
    Nat.beq (pg 5 (mask 5) (pa450010S b j) i) (ap ((pa450010tabs b).getD j #[]) i))) = true := by
  cases b
  · exact pa450010_tabs1
  · exact pa450010_tabs2

theorem pa450010_rep (b : Bool) :
    ∀ j < 4, CFSG.Sporadic.Th.Rep 28 ((pa450010tabs b).getD j #[]) (pa450010gK b j) := by
  intro j hj
  interval_cases j
  · exact rep_tabA
  · exact rep_tabB
  · cases b
    · exact rep_tabG1
    · exact rep_tabG2
  · exact rep_tabT

theorem pa450010_prepS (b : Bool) : ∀ j < 4, PRep 28 5 (pa450010S b j) (pa450010gK b j) :=
  fun j hj => CFSG.KS.PRec.prep_of_rep_tab (pa450010_rep b j hj) (allN_iff.1 (pa450010_tabs b) j hj)

theorem pa450010_perm (b : Bool) :
    allN 4 (fun j => permOK 28 5 (mask 5) (28 * 5) (pa450010S b j) (pa450010SI b j)) = true := by
  cases b
  · exact pa450010_perm1
  · exact pa450010_perm2

theorem pa450010_prepSI (b : Bool) : ∀ j < 4, PRep 28 5 (pa450010SI b j) (pa450010gK b j)⁻¹ :=
  fun j hj => CFSG.KC.OrbGroup.prep_inv (pa450010_prepS b j hj) (allN_iff.1 (pa450010_perm b) j hj)

end CertificateChecks.KernelPropA

end
