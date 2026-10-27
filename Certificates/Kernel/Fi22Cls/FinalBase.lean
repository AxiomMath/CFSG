
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs
public import Certificates.Kernel.Fi22S0.Facts
public import Certificates.Kernel.Fi22Cls.Conj
public import Certificates.Kernel.Fi22Cls.Cent
public import Certificates.Kernel.Fi22Cls.LabKill
public import Certificates.Kernel.Fi22Cls.LabKillB
public import Certificates.Kernel.Fi22Cls.LabEq
public import Certificates.Kernel.Fi22Cls.ParseEq
public import Certificates.Kernel.Fi22.Letters
public import Certificates.Kernel.Fi22Core.OrbData
public import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Data.E27.Fi22S0
public import CFSG.Certificates.Kernel.Fi22Cls.LabSound
public import CFSG.Certificates.Kernel.Fi22Cls.Sound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase
import all CFSG.Certificates.Kernel.Fi22S0.Sound

@[expose] public section

namespace CertificateChecks.KernelFi22Cls

open CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls CFSG.KD.Fi22S0 CFSG.KD.Fi22Cls CFSG.Sporadic.Fi22.S0
  CFSG.HardMathSupport.Foote.E27 CertificateChecks.KernelFi22S0

#kc_forall_tree ch13620conjAll (fun l => ch13620conj l = true) 126
  CertificateChecks.KernelFi22Cls.ch13620conj

#kc_forall_tree ch13620labAll (fun q => ch13620lab q = true) 9
  CertificateChecks.KernelFi22Cls.ch13620lab

#kc_forall_tree ch13620repAll (fun k => ch13620rep k = true) 4
  CertificateChecks.KernelFi22Cls.ch13620rep

#kc_forall_tree ch13620closAll (fun k => ch13620clos k = true) 4
  CertificateChecks.KernelFi22Cls.ch13620clos

#kc_forall_tree ch13620orbAll (fun u => ch13620orb u = true) 9
  CertificateChecks.KernelFi22Cls.ch13620orb

open CFSG.Sporadic.Fi22 (J orb gs)
open CFSG.Sporadic.Th (Rep allIn_eq_true)
open CFSG.Sporadic.Th.Native (Table compT)
open CFSG.Sporadic.Fi22.Native (chainLetters orbL orbitData)
open CFSG.KS.Fi22ClsParse (wlist)
open CFSG.Perm (pairG)
open CFSG.HardMathSupport.Foote.E27.Fi22S0 (gJ)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native (classifyOK classifyCore eqT
  lettersT eltT genT globRep labRep labCls labOf witOf conjW nR)

theorem parG : ∀ i < nS, ((par ())[i]!).1 = pp i ∧ ((par ())[i]!).2 = pj i := by
  intro i hi
  rw [par_eq, CFSG.KS.LyS0K.ofFnG (fun i => (pp i, pj i)) (by unfold nS at hi; exact hi)]
  exact ⟨rfl, rfl⟩

theorem glob_eq : ∀ k < 4, globRep[k]! = glob k := by
  intro k hk
  interval_cases k <;> rfl

theorem glob_lt : ∀ k < 4, glob k < nS := by
  intro k hk
  rw [← glob_eq k hk]
  exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three.globRep_lt k hk

theorem orb_eq : orb = orbL := by
  unfold orb
  exact CertificateChecks.KernelFi22C.orbitData_eq

theorem letters_size : (chainLetters orb).size = 32 := by
  rw [orb_eq]
  exact CertificateChecks.KernelFi22.Letters.letters.1

theorem keyAll : ∀ i < nS, key i = keyOf (tabElt gJ (par ()) i) :=
  key_eq gRAll k0_eq (blk_all (by norm_num) treeAll) parAll

theorem letRep : ∀ z < 32, RepE (LJT z) (pairG gs z) := by
  intro z hz x hx
  have h1 := ((CertificateChecks.KernelFi22.Letters.letters.2.1 z hz).2 x hx).1
  have h2 := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three.rep_chainLetters z
    (by rw [letters_size]; exact hz) x hx
  rw [orb_eq] at h2
  unfold LJT
  rw [ent_letT, ← h1]
  exact h2

theorem conjAll (l : ℕ) (hl : l < 126) :
    rep l < nS ∧ cls l < 4 ∧ wo l ≤ wo (l + 1) ∧
      (∀ t, wo l ≤ t → t < wo (l + 1) → wd t < 32) ∧
      wordJ (pairG gs) wd (wo l) (wo (l + 1) - wo l) * tabElt gJ (par ()) (rep l) =
        tabElt gJ (par ()) (glob (cls l)) * wordJ (pairG gs) wd (wo l) (wo (l + 1) - wo l) :=
  conj_of_conjC letRep gRAll tabDataK parG keyAll k0_eq glob_lt (ch13620conjAll l hl)

theorem eqT_of_rep {T T' : Table} {g h : J} (hT : Rep 3510 T g)
    (hT' : Rep 3510 T' h) (e : g = h) : eqT T T' = true := by
  unfold eqT
  rw [allIn_eq_true]
  intro i _ hi
  rw [hT i hi, hT' i hi, e, beq_self_eq_true]

theorem conjW_get {l : ℕ} (hl : l < 126) : (conjW ())[l]! = wlist wo wd l := by
  rw [conjW_eq, getElem!_pos _ l (by simp; omega)]
  simp [List.getElem_range']

theorem getOfFn {f : ℕ → ℕ} {m l : ℕ} (hl : l < m) : (Array.ofFn (n := m) fun i => f i.val)[l]! = f l :=
  CFSG.KS.LyS0K.ofFnG f hl

theorem repFacts (k : ℕ) (hk : k < 4) :
    glob k ≠ 0 ∧ tabMul (par ()) (L ()) (glob k) (tabMul (par ()) (L ()) (glob k) (glob k)) = 0 ∧
      2187 ≤ tabComm (par ()) (L ()) nS (glob k) := by
  have := CFSG.HardMathSupport.Foote.E27.Fi22S0.finite_J
  have hρ := glob_lt k hk
  obtain ⟨h0, h3⟩ := rho_of_rhoC tabDataK parG LAll hρ (ch13620repAll k hk)
  exact ⟨h0, h3, (comm_ge_of_closC tabDataK parG LAll ch13620gen_eq (ch13620closAll k hk)).2⟩

theorem comm0 : tabComm (par ()) (L ()) nS (glob 0) = 2187 := by
  have := CFSG.HardMathSupport.Foote.E27.Fi22S0.finite_J
  exact le_antisymm (comm_le_of_conjgC tabDataK parG LAll (glob_lt 0 (by norm_num)) ch13620orbAll)
    (repFacts 0 (by norm_num)).2.2

end CertificateChecks.KernelFi22Cls

end
