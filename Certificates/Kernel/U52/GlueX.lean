module

public import Certificates.Kernel.U52.Bind
public import Certificates.Kernel.U52.ChainX
public import CFSG.Certificates.Kernel.U52.PackEq
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.ClassicalGroups
public import CFSG.GH74.Statements
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Milestones.ASVolI.F48.Rest.Eng
public import CFSG.Milestones.ASVolI.F48.Rest.Perm
public import CFSG.Milestones.ASVolI.F48.Small.Base
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootRel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
public import CFSG.Sporadic.Schreier.J4SSylow
public import Certificates.Kernel.J4Count.FixCE

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelU52G

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum
  CertificateChecks.KernelU52

theorem rL : ∀ i < 4, Rng 462 9 (LP i) ∧ Rng 462 9 (LPI i) := fun i hi =>
  ⟨fun x hx => (l_range i hi x hx).1, fun x hx => (l_range i hi x hx).2⟩

theorem rE (wd : List (Fin 4 × Bool)) : Rng 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LP LPI wd) :=
  rng_evFK (by norm_num) (by norm_num) (by norm_num) rL wd

theorem cE (wd : List (Fin 4 × Bool)) :
    Canon 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LP LPI wd) :=
  canon_evFK (by norm_num) (by norm_num) (by norm_num) LP LPI wd

theorem rPC {P Q : Nat} (hP : Rng 462 9 P) (hQ : Rng 462 9 Q) :
    Rng 462 9 (pcomp 462 9 (mask 9) P Q) :=
  rng_pcomp (by norm_num) hP hQ

theorem cPC (P Q : Nat) : Canon 462 9 (pcomp 462 9 (mask 9) P Q) :=
  canon_pcomp (by norm_num) (by norm_num) P Q

theorem cId : Canon 462 9 (pidn 462 9) := canon_pidn (by norm_num) (by norm_num)

theorem rId : Rng 462 9 (pidn 462 9) := rng_pidn (by norm_num) (by norm_num)

theorem pidE : CFSG.ONSchreier.Native.pid 462 = unpack 462 9 (pidn 462 9) :=
  pid_unpack (by norm_num) (by norm_num)

theorem pcE (P : Nat) {Q : Nat} (hQ : Rng 462 9 Q) :
    CFSG.ONSchreier.Native.pcomp 462 (unpack 462 9 P) (unpack 462 9 Q) =
      unpack 462 9 (pcomp 462 9 (mask 9) P Q) :=
  pcomp_unpackR (by norm_num) P hQ

theorem peqE {P Q : Nat} (hP : Canon 462 9 P) (hQ : Canon 462 9 Q) :
    CFSG.ONSchreier.Native.peq 462 (unpack 462 9 P) (unpack 462 9 Q) = Nat.beq P Q :=
  peq_unpackC (by norm_num) hP hQ

theorem containsE {α : Type} (f : α → Nat) (hf : ∀ x, Canon 462 9 (f x)) (l : List α) {Q : Nat}
    (hQ : Canon 462 9 Q) :
    (l.map fun x => unpack 462 9 (f x)).contains (unpack 462 9 Q) =
      l.any fun x => Nat.beq Q (f x) :=
  contains_map_unpackC (by norm_num) f hf l hQ

theorem gBind : ∀ j < 6, arrBind (burnsideF48t_u52Gens ())[j]! 462 9 (CX.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem xPerm : allN 12 (fun j => permOK 462 9 (mask 9) (462 * 9) (CX.S j) (CX.SI j)) = true :=
  (Orb.head_facts CX.head).1

theorem gPerm : ∀ j < 6, permOK 462 9 (mask 9) (462 * 9) (CX.S j) (CX.SI j) = true :=
  fun j hj => allN_spec xPerm j (by omega)

theorem rS : ∀ j < 6, Rng 462 9 (CX.S j) := fun j hj => rng_of_permOK (gPerm j hj)

theorem cS : ∀ j < 6, Canon 462 9 (CX.S j) := fun j hj => canon_of_permOK (gPerm j hj)

theorem g_eq : ∀ j < 6, (burnsideF48t_u52Gens ())[j]! = unpack 462 9 (CX.S j) :=
  fun j hj => arrBind_sound (gBind j hj)

theorem gi_eq : ∀ j < 6, (burnsideF48t_u52GensInv ())[j]! = unpack 462 9 (CX.SI j) := by
  intro j hj
  have hs : (burnsideF48t_u52Gens ()).size = 6 := by decide +kernel
  rw [burnsideF48t_u52GensInv, getElem!_pos _ j (by simp [hs, hj]), Array.getElem_map,
    ← getElem!_pos _ j (by omega), g_eq j hj]
  exact pinvCand_unpack (gPerm j hj)

theorem gens_eq : burnsideF48t_u52Gens () = #[unpack 462 9 (CX.S 0), unpack 462 9 (CX.S 1),
    unpack 462 9 (CX.S 2), unpack 462 9 (CX.S 3), unpack 462 9 (CX.S 4), unpack 462 9 (CX.S 5)] := by
  have hs : (burnsideF48t_u52Gens ()).size = 6 := by decide +kernel
  apply Array.ext
  · rw [hs]
    rfl
  · intro j h1 _
    rw [← getElem!_pos _ j h1, g_eq j (by omega)]
    rw [hs] at h1
    interval_cases j <;> rfl

theorem xBinds : Binds 462 9 CX.S 12 5 CX.BP
    (CFSG.Sporadic.HNOddCore.strongArrs 462 (burnsideF48t_u52Gens ()) burnsideF48t_u52WX)
    (burnsideF48t_u52BaseX.map Fin.val).toArray :=
  binds_of (O := burnsideF48t_u52Gens ()) (W := burnsideF48t_u52WX)
    (base := burnsideF48t_u52BaseX)
    ⟨by decide +kernel, fun j hj => arrBind_sound (gBind j hj)⟩ (by decide +kernel) (by norm_num)
    ⟨by decide +kernel, by decide +kernel⟩ CX.head

theorem siftX_eq {G : Nat} (hG : Canon 462 9 G) (hr : Rng 462 9 G) :
    burnsideF48t_sift 462 (burnsideF48t_u52LevX ()) burnsideF48t_u52BaseX (unpack 462 9 G) =
      siftK 462 9 (mask 9) (462 * 9) (pidn 462 9) CX.LR CX.TRI CX.BP 5 0 G := by
  rw [burnsideF48t_sift, burnsideF48t_u52LevX, burnsideF48t_levels, burnsideF48t_baseArr]
  exact sift_unpack xBinds xPerm CX.hl hG hr

end CertificateChecks.KernelU52G

end
