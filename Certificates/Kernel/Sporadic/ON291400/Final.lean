module

public import Certificates.Kernel.Sporadic.ON291400.Chk
public import Certificates.Kernel.Sporadic.OddCore.ON2129F
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRankInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON291400

open CFSG.ONSchreier CFSG.PSL3Four.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KS.PEnum CFSG.KC.BfsPin CertificateChecks.KernelSpor.ON2129
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
open CFSG.KLie.CT (fget andB orB notB)

abbrev Cn (p : Nat) : Prop := canonK 32 6 (mask 6) (32 * 6) p = true

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl
theorem natbeq (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · exact beq_false_of_ne fun e => by rw [e, Nat.beq_refl] at h; exact Bool.noConfusion h
  · rw [Nat.eq_of_beq_eq_true h]
    exact beq_self_eq_true _

theorem allBelow_eqN {m : Nat} {f g : Nat → Bool} (h : ∀ i < m, f i = g i) :
    allBelow m f = allN m g := by
  rw [Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.Raw.Orb.allN_iff]
  exact forall_congr' fun i => imp_congr_right fun hi => by rw [h i hi]

theorem sel : (List.range 512).filter qI = ISel ∧ ISel.length = 87 := by
  obtain ⟨h1, h2⟩ := (by simpa only [bAnd_iff] using k_sel :
    selFrom qI 512 0 ISel = true ∧ Nat.beq ISel.length 87 = true)
  exact ⟨sel_spec h1, Nat.eq_of_beq_eq_true h2⟩

theorem getD_get {i : Nat} (hi : i < 87) : ISel.getD i 0 = ISel[i]'(by rw [sel.2]; exact hi) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [sel.2]; exact hi),
    Option.getD_some]

theorem sel_lt {i : Nat} (hi : i < 87) : ISel.getD i 0 < 512 := by
  have hm : ISel.getD i 0 ∈ ISel := by
    rw [getD_get hi]
    exact List.getElem_mem _
  rw [← sel.1, List.mem_filter, List.mem_range] at hm
  exact hm.1

theorem ipt_eq {i : Nat} (hi : i < 87) : IPT i = T32E.T (ISel.getD i 0) :=
  Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 k_bind i hi)

theorem cI {i : Nat} (hi : i < 87) : Cn (IPT i) := by
  rw [ipt_eq hi]
  exact penumPt_canon (t32_pt (sel_lt hi))

theorem beqU {p q : Nat} (hp : Cn p) (hq : Cn q) : (unpack 32 6 p == unpack 32 6 q) = Nat.beq p q :=
  CFSG.KS.PEnum.beq_unpack hp hq

theorem invTabs_eq : invTabs () = Array.ofFn (n := 87) fun i => unpack 32 6 (IPT i.val) := by
  unfold invTabs
  rw [t32Enum_eq, penumRec_eq]
  dsimp only
  rw [filter_ofFn (m := T32E.cnt) (f := fun i => unpack 32 6 (T32E.T i))]
  have hc : T32E.cnt = 512 := rfl
  have e : ((List.range T32E.cnt).filter fun i =>
      (comp 32 (unpack 32 6 (T32E.T i)) (unpack 32 6 (T32E.T i)) == idTab 32 &&
        !(unpack 32 6 (T32E.T i) == idTab 32))) = ISel := by
    rw [hc, ← sel.1]
    apply List.filter_congr
    intro i hi
    have hi' : i < 512 := List.mem_range.1 hi
    have ct := penumPt_canon (t32_pt (hc ▸ hi'))
    unfold qI
    rw [CFSG.KS.PEnum.strictB_app', andB_eq, notB_eq, comp_unpack ct ct, idTab_eq,
      beqU (canonK_pcomp ct ct) idCanon.1, beqU ct idCanon.1]
    rfl
  rw [e]
  apply Array.ext (by simp [sel.2])
  intro i h1 h2
  have hi : i < 87 := by simpa using h2
  simp only [List.getElem_toArray, List.getElem_map, Array.getElem_ofFn]
  rw [ipt_eq hi, getD_get hi]

theorem I_get {i : Nat} (hi : i < 87) : (invTabs ())[i]! = unpack 32 6 (IPT i) := by
  rw [invTabs_eq, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem I_size : (invTabs ()).size = 87 := by rw [invTabs_eq, Array.size_ofFn]

theorem cm_eq {i l : Nat} (hi : i < 87) (hl : l < 87) :
    (comp 32 (unpack 32 6 (IPT i)) (unpack 32 6 (IPT l)) ==
      comp 32 (unpack 32 6 (IPT l)) (unpack 32 6 (IPT i))) = cmB i l := by
  rw [comp_unpack (cI hi) (cI hl), comp_unpack (cI hl) (cI hi),
    beqU (canonK_pcomp (cI hi) (cI hl)) (canonK_pcomp (cI hl) (cI hi))]
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 k_cm i hi) l hl
  unfold bEqK pc at h
  cases hb : cmB i l <;> rw [hb] at h
  · cases hx : Nat.beq (pcomp 32 6 (mask 6) (IPT i) (IPT l)) (pcomp 32 6 (mask 6) (IPT l) (IPT i))
    · rfl
    · rw [hx] at h
      exact absurd h (by decide)
  · exact h

theorem C_get {i l : Nat} (hi : i < 87) (hl : l < 87) :
    ((commMat (invTabs ()))[i]!)[l]! = cmB i l := by
  unfold commMat
  rw [getElem!_pos _ i (by simpa [I_size] using hi), Array.getElem_map,
    getElem!_pos _ l (by simpa [I_size] using hl), Array.getElem_map,
    ← getElem!_pos (invTabs ()) i (by simpa [I_size] using hi),
    ← getElem!_pos (invTabs ()) l (by simpa [I_size] using hl), I_get hi, I_get hl]
  exact cm_eq hi hl

theorem fourth_eq {i j k : Nat} (hi : i < 87) (hj : j < 87) (hk : k < 87) :
    fourthOK (invTabs ()) (commMat (invTabs ())) i j k = fourthK i j k := by
  unfold fourthOK fourthK
  simp only [CFSG.KS.PEnum.strictB_app']
  rw [I_size]
  apply allBelow_eqN
  intro l hl
  rw [C_get hi hl, C_get hj hl, C_get hk hl, I_get hi, I_get hj, I_get hk, I_get hl,
    comp_unpack (cI hi) (cI hj), comp_unpack (cI hi) (cI hk), comp_unpack (cI hj) (cI hk),
    comp_unpack (canonK_pcomp (cI hi) (cI hj)) (cI hk), beqU (cI hl) (cI hi), beqU (cI hl) (cI hj), beqU (cI hl) (cI hk),
    beqU (cI hl) (canonK_pcomp (cI hi) (cI hj)), beqU (cI hl) (canonK_pcomp (cI hi) (cI hk)),
    beqU (cI hl) (canonK_pcomp (cI hj) (cI hk)),
    beqU (cI hl) (canonK_pcomp (canonK_pcomp (cI hi) (cI hj)) (cI hk))]
  simp only [orB_eq, andB_eq, notB_eq, Bool.or_assoc, pc]

theorem third_eq {i j : Nat} (hi : i < 87) (hj : j < 87) :
    thirdOK (invTabs ()) (commMat (invTabs ())) i j = thirdK i j := by
  unfold thirdOK thirdK
  simp only [CFSG.KS.PEnum.strictB_app']
  rw [I_size]
  apply allBelow_eqN
  intro k hk
  rw [C_get hi hk, C_get hj hk, I_get hi, I_get hj, I_get hk, comp_unpack (cI hi) (cI hj),
    beqU (cI hk) (canonK_pcomp (cI hi) (cI hj)), fourth_eq hi hj hk, natbeq, natbeq]
  simp only [orB_eq, andB_eq, notB_eq, Bool.or_assoc, pc]

theorem noE16_eq : noE16Check () = noE16K := by
  unfold noE16Check noE16K
  dsimp only
  rw [I_size]
  apply allBelow_eqN
  intro i hi
  apply allBelow_eqN
  intro j hj
  rw [C_get hi hj, third_eq hi hj, natbeq]
  simp only [orB_eq, notB_eq, Bool.or_assoc]

theorem noE16_true : noE16Check () = true := by
  rw [noE16_eq]
  exact k_main

end CertificateChecks.KernelSpor.ON291400

end
