
module

public import Certificates.Kernel.Fi23M.Stab
public import CFSG.Sporadic.Fi23.SimpleBase
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Presentation.Fi23
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Fi23.SetupBase
import Certificates.Kernel.Sporadic.Fi23Br.Rels
import Mathlib
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.F3.SepSpec
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Fi23.CertificateBase
public import CFSG.Sporadic.Fi23.SlpSpec
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.KD.Fi23K CFSG.KC.Fi23K CFSG.KS.PC CFSG.Sporadic.Fi23 CFSG.Sporadic.Bridge.Fi23GPL.Native
  TauCeti

open CFSG.Sporadic.Fi23.Native (dWord)

abbrev M253 :=Matrix (Fin 253) (Fin 253) (ZMod 3)

abbrev PG := PresentedGroup P23.relatorSet

theorem sq_rel : ∀ k < 10, [(k, true), (k, true)] ∈ rels () := by decide +kernel

theorem rels_lt : ∀ w ∈ rels (), ∀ l ∈ w, l.1 < 10 := by decide +kernel

section

noncomputable def gen (k : ℕ) : PG :=
  if h : k < P23.generatorCount then PresentedGroup.of ⟨k, h⟩ else 1

theorem phiX_gen {k : ℕ} (hk : k < 10) : phiX (gen k) = xS k := by
  unfold gen
  rw [dif_pos (by rw [generatorCount_P23]; exact hk)]
  exact presHom_of P23 xS rels_X _

noncomputable def wordP (w : List ℕ) : PG := (w.map gen).prod

theorem phiX_wordP {w : List ℕ} (hw : ∀ k ∈ w, k < 10) : phiX (wordP w) = (w.map xS).prod := by
  unfold wordP
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun k hk => phiX_gen (hw k hk)

theorem sw_lt {i : ℕ} (hi : i < 2) : ∀ k ∈ sw i, k < 10 := by
  obtain ⟨-, -, -, -, -, -, hx0, hx1⟩ := surj_data
  interval_cases i
  · exact hx0
  · exact hx1

noncomputable def wα : PG := wordP (sw 0)
noncomputable def wβ : PG := wordP (sw 1)

theorem phiX_wα : ActsAs (phiX wα) (tb G 39) := by
  unfold wα
  rw [phiX_wordP (sw_lt (by norm_num))]
  exact alpha_acts

theorem phiX_wβ : ActsAs (phiX wβ) (tb G 40) := by
  unfold wβ
  rw [phiX_wordP (sw_lt (by norm_num))]
  exact beta_acts

noncomputable def wZ : PG := (dWord.map fun x => if x = 0 then wα else wβ).prod

noncomputable def wD : PG := wZ ^ 7

theorem acts_one : ActsAs 1 (fun x => x) := fun _ _ => rfl

theorem eq136 : EL 136 = [42] ∧ ER 136 = dWord.map fun x => if x = 0 then 39 else 40 := by
  decide +kernel

theorem eq137 : EL 137 = [43] ∧ ER 137 = List.replicate 7 42 := by decide +kernel

theorem acts_wv : ∀ v : List ℕ,
    ActsAs (phiX (v.map fun x => if x = 0 then wα else wβ).prod)
      (wv G (v.map fun x => if x = 0 then 39 else 40))
  | [] => by
    rw [List.map_nil, List.prod_nil, map_one]
    exact acts_one
  | x :: v => by
    rw [List.map_cons, List.prod_cons, map_mul, List.map_cons]
    have h2 := acts_wv v
    by_cases h0 : x = 0
    · rw [if_pos h0, if_pos h0]
      exact phiX_wα.mul h2
    · rw [if_neg h0, if_neg h0]
      exact phiX_wβ.mul h2

theorem phiX_wZ : ActsAs (phiX wZ) (tb G 42) := by
  intro x hx
  unfold wZ
  rw [acts_wv dWord x hx]
  have h := eqv (k := 136) (by norm_num) hx
  rw [eq136.1, eq136.2] at h
  simp only [wv_cons, wv_nil] at h
  exact h.symm

theorem acts_pow {p : Equiv.Perm (Fin 31671)} {r : ℕ} (hp : ActsAs p (tb G r)) :
    ∀ n, ActsAs (p ^ n) (wv G (List.replicate n r))
  | 0 => by
    rw [pow_zero]
    exact acts_one
  | n + 1 => by
    rw [pow_succ']
    exact hp.mul (acts_pow hp n)

theorem phiX_wD : ActsAs (phiX wD) (tb G 43) := by
  have h7 : ActsAs (phiX wD) (wv G (List.replicate 7 42)) := by
    unfold wD
    rw [map_pow]
    exact acts_pow phiX_wZ 7
  intro x hx
  rw [h7 x hx]
  have h := eqv (k := 137) (by norm_num) hx
  rw [eq137.1, eq137.2] at h
  simp only [wv_cons, wv_nil] at h
  exact h.symm

theorem phiX_mem (g : PG) : phiX g ∈ Xc := by
  rw [← range_phiX]
  exact ⟨g, rfl⟩

theorem stab_comm {g : PG} (h0 : phiX g ⟨0, hn⟩ = ⟨0, hn⟩) :
    g * wD = wD * g := by
  apply phiX_injective
  rw [map_mul, map_mul]
  exact H1_comm phiX_wD _ (stab_mem (phiX_mem g) h0)

end

end CertificateChecks.KernelFi23M

end
